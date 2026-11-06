import NetHack.Soko22Hazard87.EqIntroBlocks0036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro9250 (p : Pattern) (selected : d117400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9248 q selected
    | true =>
      simp only [d117391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9249 q selected
  have h2 (q : Pattern) (selected : d117392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117394 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9249 q selected
    | true =>
      simp only [d117394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117395 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117396 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117397 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117398 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117399 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117400 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9251 (p : Pattern) (selected : d117404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117394 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9249 q selected
    | true =>
      simp only [d117394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117395 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117396 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117398 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117403 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117404 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9252 (p : Pattern) (selected : d117410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117401 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9250 q selected
    | true =>
      simp only [d117401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117402 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9251 q selected
    | true =>
      simp only [d117405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117409 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9253 (p : Pattern) (selected : d117414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9251 q selected
    | true =>
      simp only [d117405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117411 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117412 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117413 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117414 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9254 (p : Pattern) (selected : d117426 p = 1) : d121670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117384 q = 1) : d117384 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117415 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9252 q selected
    | true =>
      simp only [d117415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9253 q selected
  have h3 (q : Pattern) (selected : d117416 q = 1) : d121666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117416, d121666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117416, d121666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117422 q = 1) : d117422 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d117423 q = 1) : d121667 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117423, d121667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117423, d121667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117424 q = 1) : d121668 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117424, d121668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117424, d121668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117425 q = 1) : d121669 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117425, d121669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117425, d121669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117426 q = 1) : d121670 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117426, d121670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117426, d121670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9255 (p : Pattern) (selected : d117443 p = 1) : d121676 p = 1 := by
  have h0 (q : Pattern) (selected : d117201 q = 1) : d117201 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117311 q = 1) : d121654 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117311, d121654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9243 q selected
    | true =>
      simp only [d117311, d121654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9246 q selected
  have h2 (q : Pattern) (selected : d117324 q = 1) : d117324 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117325 q = 1) : d121655 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117325, d121655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117325, d121655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d117326 q = 1) : d121656 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117326, d121656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117326, d121656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117327 q = 1) : d121657 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117327, d121657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117327, d121657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117331 q = 1) : d121661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117331, d121661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117331, d121661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9247 q selected
  have h8 (q : Pattern) (selected : d117333 q = 1) : d117333 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d117334 q = 1) : d121662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117334, d121662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117334, d121662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117335 q = 1) : d121663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117335, d121663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117335, d121663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d117336 q = 1) : d121664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117336, d121664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117336, d121664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d117337 q = 1) : d121665 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117337, d121665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117337, d121665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117427 q = 1) : d121671 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117427, d121671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117427, d121671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9254 q selected
  have h14 (q : Pattern) (selected : d117438 q = 1) : d117438 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d117439 q = 1) : d121672 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117439, d121672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d117439, d121672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117440 q = 1) : d121673 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117440, d121673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117440, d121673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d117441 q = 1) : d121674 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117441, d121674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117441, d121674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d117442 q = 1) : d121675 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117442, d121675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d117442, d121675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d117443 q = 1) : d121676 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d117443, d121676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117443, d121676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro9256 (p : Pattern) (selected : d117449 p = 1) : d121682 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117444 q = 1) : d121677 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d117444, d121677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117444, d121677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9255 q selected
  have h2 (q : Pattern) (selected : d117445 q = 1) : d121678 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d117445, d121678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117445, d121678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117446 q = 1) : d121679 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d117446, d121679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117446, d121679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117447 q = 1) : d121680 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d117447, d121680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117447, d121680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117448 q = 1) : d121681 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d117448, d121681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117448, d121681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117449 q = 1) : d121682 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d117449, d121682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117449, d121682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9257 (p : Pattern) (selected : d1253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1237 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro49 q selected
    | true =>
      simp only [d1237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro76 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1238 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1249 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h4 (q : Pattern) (selected : d1250 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1251 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d862 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro50 q selected
    | true =>
      simp only [d862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d863 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d864 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1252 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1253 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro9258 (p : Pattern) (selected : d1263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1249 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro29 q selected
    | true =>
      simp only [d1249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1250 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1259 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d1259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h4 (q : Pattern) (selected : d1260 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d1261 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d344 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro14 q selected
    | true =>
      simp only [d344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h7 (q : Pattern) (selected : d345 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d346 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1262 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1263 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro9259 (p : Pattern) (selected : d117561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117553 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9257 q selected
    | true =>
      simp only [d117553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117554 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117555 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117556 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117557 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9258 q selected
    | true =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117558 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117559 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117560 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117561 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9260 (p : Pattern) (selected : d1274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1270 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h2 (q : Pattern) (selected : d1271 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d164 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
    | true =>
      simp only [d164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d165 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1272 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d166 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1273 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1274 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9261 (p : Pattern) (selected : d117566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117557 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9258 q selected
    | true =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117558 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117559 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117560 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
    | true =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117563 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117564 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117565 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117566 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9262 (p : Pattern) (selected : d117570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
    | true =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117563 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117564 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117565 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117570 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9263 (p : Pattern) (selected : d117577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117567 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9259 q selected
    | true =>
      simp only [d117567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9261 q selected
  have h2 (q : Pattern) (selected : d117568 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117569 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117571 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9261 q selected
    | true =>
      simp only [d117571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9262 q selected
  have h5 (q : Pattern) (selected : d117572 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117573 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117574 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117575 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117576 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117577 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9264 (p : Pattern) (selected : d117581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117571 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9261 q selected
    | true =>
      simp only [d117571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9262 q selected
  have h2 (q : Pattern) (selected : d117572 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117573 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117575 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117581 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9265 (p : Pattern) (selected : d117587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9263 q selected
    | true =>
      simp only [d117578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117582 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9264 q selected
    | true =>
      simp only [d117582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117583 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117584 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117585 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117586 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117587 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9266 (p : Pattern) (selected : d117591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117582 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9264 q selected
    | true =>
      simp only [d117582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117583 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117588 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117589 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117590 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117591 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9267 (p : Pattern) (selected : d117603 p = 1) : d121689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117517 q = 1) : d117517 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117526 q = 1) : d117526 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117552 q = 1) : d117552 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d117592 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9265 q selected
    | true =>
      simp only [d117592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9266 q selected
  have h5 (q : Pattern) (selected : d117593 q = 1) : d121685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117593, d121685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117593, d121685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117599 q = 1) : d117599 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d117600 q = 1) : d121686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117600, d121686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117600, d121686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117601 q = 1) : d121687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117601, d121687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117601, d121687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117602 q = 1) : d121688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117602, d121688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117602, d121688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117603 q = 1) : d121689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117603, d121689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117603, d121689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro9268 (p : Pattern) (selected : d117617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9263 q selected
    | true =>
      simp only [d117578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117582 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9264 q selected
    | true =>
      simp only [d117582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117583 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117584 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117585 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117586 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117617 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9269 (p : Pattern) (selected : d117618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117582 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9264 q selected
    | true =>
      simp only [d117582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117583 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117588 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117589 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117590 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117618 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9270 (p : Pattern) (selected : d117627 p = 1) : d121694 p = 1 := by
  have h0 (q : Pattern) (selected : d117517 q = 1) : d117517 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117526 q = 1) : d117526 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117552 q = 1) : d117552 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117592 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9265 q selected
    | true =>
      simp only [d117592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9266 q selected
  have h4 (q : Pattern) (selected : d117593 q = 1) : d121685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117593, d121685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117593, d121685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117599 q = 1) : d117599 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d117600 q = 1) : d121686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117600, d121686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117600, d121686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117601 q = 1) : d121687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117601, d121687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117601, d121687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117602 q = 1) : d121688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117602, d121688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117602, d121688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117609 q = 1) : d117609 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d117614 q = 1) : d117614 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d117616 q = 1) : d117616 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d117619 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9268 q selected
    | true =>
      simp only [d117619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9269 q selected
  have h13 (q : Pattern) (selected : d117620 q = 1) : d121690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117620, d121690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117620, d121690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117623 q = 1) : d117623 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d117624 q = 1) : d121691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117624, d121691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d117624, d121691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117625 q = 1) : d121692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117625, d121692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117625, d121692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117626 q = 1) : d121693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117626, d121693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117626, d121693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d117627 q = 1) : d121694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117627, d121694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117627, d121694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro9271 (p : Pattern) (selected : d117647 p = 1) : d121701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117616 q = 1) : d117616 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117619 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9268 q selected
    | true =>
      simp only [d117619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9269 q selected
  have h3 (q : Pattern) (selected : d117620 q = 1) : d121690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117620, d121690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117620, d121690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117623 q = 1) : d117623 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d117624 q = 1) : d121691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117624, d121691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117624, d121691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117645 q = 1) : d121699 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117645, d121699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117645, d121699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117646 q = 1) : d121700 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117646, d121700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117646, d121700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117647 q = 1) : d121701 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117647, d121701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117647, d121701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9272 (p : Pattern) (selected : d117724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9257 q selected
  have h2 (q : Pattern) (selected : d117553 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9257 q selected
    | true =>
      simp only [d117553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117554 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117718 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117719 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117720 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9258 q selected
  have h8 (q : Pattern) (selected : d117557 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9258 q selected
    | true =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117721 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117558 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117722 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117723 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117724 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9273 (p : Pattern) (selected : d117729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117720 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9258 q selected
  have h2 (q : Pattern) (selected : d117557 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9258 q selected
    | true =>
      simp only [d117557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117721 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117558 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117722 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117723 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
  have h8 (q : Pattern) (selected : d117562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
    | true =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117563 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d117727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d117728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d117729 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9274 (p : Pattern) (selected : d117733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117725 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
  have h2 (q : Pattern) (selected : d117562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9260 q selected
    | true =>
      simp only [d117562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117726 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117563 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117727 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117728 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117733 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9275 (p : Pattern) (selected : d117740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117730 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9272 q selected
    | true =>
      simp only [d117730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9273 q selected
  have h2 (q : Pattern) (selected : d117731 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117732 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117734 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9273 q selected
    | true =>
      simp only [d117734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9274 q selected
  have h5 (q : Pattern) (selected : d117735 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117736 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117737 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117738 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117739 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117740 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9276 (p : Pattern) (selected : d117744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117734 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9273 q selected
    | true =>
      simp only [d117734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9274 q selected
  have h2 (q : Pattern) (selected : d117735 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117736 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117738 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117743 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117744 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9277 (p : Pattern) (selected : d117750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117741 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9275 q selected
    | true =>
      simp only [d117741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117742 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9276 q selected
    | true =>
      simp only [d117745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117750 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9278 (p : Pattern) (selected : d117754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9276 q selected
    | true =>
      simp only [d117745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117751 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117754 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9279 (p : Pattern) (selected : d117766 p = 1) : d121711 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117715 q = 1) : d117715 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117755 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9277 q selected
    | true =>
      simp only [d117755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9278 q selected
  have h3 (q : Pattern) (selected : d117756 q = 1) : d121707 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117756, d121707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117756, d121707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117762 q = 1) : d117762 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d117763 q = 1) : d121708 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117763, d121708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117763, d121708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117764 q = 1) : d121709 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117764, d121709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117764, d121709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117765 q = 1) : d121710 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117765, d121710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117765, d121710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117766 q = 1) : d121711 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117766, d121711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117766, d121711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9280 (p : Pattern) (selected : d117783 p = 1) : d121717 p = 1 := by
  have h0 (q : Pattern) (selected : d117509 q = 1) : d117509 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117628 q = 1) : d121695 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117628, d121695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9267 q selected
    | true =>
      simp only [d117628, d121695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9270 q selected
  have h2 (q : Pattern) (selected : d117641 q = 1) : d117641 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117642 q = 1) : d121696 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117642, d121696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117642, d121696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d117643 q = 1) : d121697 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117643, d121697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117643, d121697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117644 q = 1) : d121698 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117644, d121698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117644, d121698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117648 q = 1) : d121702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117648, d121702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117648, d121702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9271 q selected
  have h8 (q : Pattern) (selected : d117650 q = 1) : d117650 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d117651 q = 1) : d121703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117651, d121703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117651, d121703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117652 q = 1) : d121704 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117652, d121704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117652, d121704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d117653 q = 1) : d121705 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117653, d121705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117653, d121705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d117654 q = 1) : d121706 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117654, d121706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117654, d121706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117767 q = 1) : d121712 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117767, d121712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117767, d121712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9279 q selected
  have h14 (q : Pattern) (selected : d117778 q = 1) : d117778 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d117779 q = 1) : d121713 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d117779, d121713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d117779, d121713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117780 q = 1) : d121714 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d117780, d121714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d117780, d121714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d117781 q = 1) : d121715 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d117781, d121715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d117781, d121715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d117782 q = 1) : d121716 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d117782, d121716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d117782, d121716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d117783 q = 1) : d121717 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d117783, d121717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117783, d121717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro9281 (p : Pattern) (selected : d117789 p = 1) : d121723 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117784 q = 1) : d121718 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d117784, d121718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117784, d121718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9280 q selected
  have h2 (q : Pattern) (selected : d117785 q = 1) : d121719 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d117785, d121719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117785, d121719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117786 q = 1) : d121720 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d117786, d121720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117786, d121720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117787 q = 1) : d121721 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d117787, d121721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117787, d121721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117788 q = 1) : d121722 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d117788, d121722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117788, d121722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117789 q = 1) : d121723 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d117789, d121723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117789, d121723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9282 (p : Pattern) (selected : d1724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1695 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro106 q selected
    | true =>
      simp only [d1695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro107 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro76 q selected
  have h3 (q : Pattern) (selected : d1697 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1714 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro110 q selected
    | true =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro111 q selected
  have h5 (q : Pattern) (selected : d1715 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h6 (q : Pattern) (selected : d1716 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1717 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1705 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro109 q selected
    | true =>
      simp only [d1705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d1706 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d1720 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d1721 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d1722 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1723 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1724 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d1724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h14 p selected
theorem eqIntro9283 (p : Pattern) (selected : d1739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d1714 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro110 q selected
    | true =>
      simp only [d1714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro111 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1715 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro78 q selected
  have h3 (q : Pattern) (selected : d1716 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1731 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
  have h5 (q : Pattern) (selected : d1270 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h6 (q : Pattern) (selected : d1732 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1733 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1720 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro112 q selected
    | true =>
      simp only [d1720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d1721 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d1735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
    | true =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d1736 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d1737 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1738 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1739 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d1739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h14 p selected
theorem eqIntro9284 (p : Pattern) (selected : d117919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117911 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9282 q selected
    | true =>
      simp only [d117911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117912 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117913 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117914 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117915 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9283 q selected
    | true =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117916 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117917 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117918 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117919 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9285 (p : Pattern) (selected : d1751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1746 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro114 q selected
  have h2 (q : Pattern) (selected : d1270 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro0 q selected
  have h3 (q : Pattern) (selected : d1747 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
    | true =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1736 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1748 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1749 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1750 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1751 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro9286 (p : Pattern) (selected : d117924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117915 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9283 q selected
    | true =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117916 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117917 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117918 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117920 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9285 q selected
    | true =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117921 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117922 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117923 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d117924 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9287 (p : Pattern) (selected : d10213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
  have h2 (q : Pattern) (selected : d10210 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1735 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro115 q selected
    | true =>
      simp only [d1735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1736 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10211 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1749 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10212 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10213 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9288 (p : Pattern) (selected : d117932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117928 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
    | true =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117929 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117930 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117931 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117932 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9289 (p : Pattern) (selected : d117937 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117920 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9285 q selected
    | true =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117921 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d117922 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d117922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117923 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d117923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117937 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d117937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9290 (p : Pattern) (selected : d117943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117925 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9284 q selected
    | true =>
      simp only [d117925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9286 q selected
  have h2 (q : Pattern) (selected : d117926 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117927 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117933 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9286 q selected
    | true =>
      simp only [d117933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9288 q selected
  have h5 (q : Pattern) (selected : d117934 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117935 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117936 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117938 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9286 q selected
    | true =>
      simp only [d117938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9289 q selected
  have h9 (q : Pattern) (selected : d117939 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117940 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d117941 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d117942 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d117943 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d117943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9291 (p : Pattern) (selected : d117947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117938 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d117938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9286 q selected
    | true =>
      simp only [d117938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9289 q selected
  have h2 (q : Pattern) (selected : d117939 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d117939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117940 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d117940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117941 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d117941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117946 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d117946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117947 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d117947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9292 (p : Pattern) (selected : d117953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117944 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9290 q selected
    | true =>
      simp only [d117944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117945 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117948 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9291 q selected
    | true =>
      simp only [d117948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117949 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117950 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117951 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117952 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117953 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9293 (p : Pattern) (selected : d117957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117948 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9291 q selected
    | true =>
      simp only [d117948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117949 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117954 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117955 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9294 (p : Pattern) (selected : d117969 p = 1) : d121731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117866 q = 1) : d117866 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117875 q = 1) : d117875 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117910 q = 1) : d117910 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d117958 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9292 q selected
    | true =>
      simp only [d117958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9293 q selected
  have h5 (q : Pattern) (selected : d117959 q = 1) : d121727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117959, d121727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117959, d121727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117965 q = 1) : d117965 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d117966 q = 1) : d121728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117966, d121728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117966, d121728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117967 q = 1) : d121729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117967, d121729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117967, d121729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117968 q = 1) : d121730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117968, d121730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117968, d121730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117969 q = 1) : d121731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117969, d121731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117969, d121731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro9295 (p : Pattern) (selected : d117984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117944 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9290 q selected
    | true =>
      simp only [d117944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117945 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117948 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9291 q selected
    | true =>
      simp only [d117948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117949 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117950 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117951 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d117952 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d117952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d117984 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d117984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9296 (p : Pattern) (selected : d117985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117948 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d117948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9291 q selected
    | true =>
      simp only [d117948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d117949 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d117949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d117954 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d117954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d117955 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d117955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d117956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d117956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d117985 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d117985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d117985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9297 (p : Pattern) (selected : d117994 p = 1) : d121736 p = 1 := by
  have h0 (q : Pattern) (selected : d117866 q = 1) : d117866 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117875 q = 1) : d117875 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117910 q = 1) : d117910 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d117958 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9292 q selected
    | true =>
      simp only [d117958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9293 q selected
  have h4 (q : Pattern) (selected : d117959 q = 1) : d121727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117959, d121727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117959, d121727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d117965 q = 1) : d117965 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d117966 q = 1) : d121728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117966, d121728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d117966, d121728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d117967 q = 1) : d121729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117967, d121729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117967, d121729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d117968 q = 1) : d121730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117968, d121730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117968, d121730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d117975 q = 1) : d117975 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d117980 q = 1) : d117980 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d117983 q = 1) : d117983 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d117986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9295 q selected
    | true =>
      simp only [d117986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9296 q selected
  have h13 (q : Pattern) (selected : d117987 q = 1) : d121732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117987, d121732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d117987, d121732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d117990 q = 1) : d117990 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d117991 q = 1) : d121733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117991, d121733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d117991, d121733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d117992 q = 1) : d121734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d117992, d121734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d117992, d121734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d117993 q = 1) : d121735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d117993, d121735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d117993, d121735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d117994 q = 1) : d121736 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d117994, d121736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117994, d121736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro9298 (p : Pattern) (selected : d118019 p = 1) : d121743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117983 q = 1) : d117983 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9295 q selected
    | true =>
      simp only [d117986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9296 q selected
  have h3 (q : Pattern) (selected : d117987 q = 1) : d121732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d117987, d121732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117987, d121732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117990 q = 1) : d117990 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d117991 q = 1) : d121733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d117991, d121733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117991, d121733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118017 q = 1) : d121741 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118017, d121741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118017, d121741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118018 q = 1) : d121742 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118018, d121742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118018, d121742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118019 q = 1) : d121743 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118019, d121743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118019, d121743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9299 (p : Pattern) (selected : d118105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118097 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9282 q selected
  have h2 (q : Pattern) (selected : d117911 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9282 q selected
    | true =>
      simp only [d117911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117912 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118099 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118101 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9283 q selected
  have h8 (q : Pattern) (selected : d117915 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9283 q selected
    | true =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118102 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117916 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118103 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118104 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118105 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9300 (p : Pattern) (selected : d118110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118101 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9283 q selected
  have h2 (q : Pattern) (selected : d117915 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9283 q selected
    | true =>
      simp only [d117915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118102 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117916 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118103 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118104 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9285 q selected
  have h8 (q : Pattern) (selected : d117920 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9285 q selected
    | true =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d117921 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118110 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9301 (p : Pattern) (selected : d118118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118114 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
  have h2 (q : Pattern) (selected : d117928 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9287 q selected
    | true =>
      simp only [d117928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118115 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117929 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118116 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118117 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118118 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9302 (p : Pattern) (selected : d118123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9285 q selected
  have h2 (q : Pattern) (selected : d117920 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9285 q selected
    | true =>
      simp only [d117920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117921 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d117921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118123 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9303 (p : Pattern) (selected : d118129 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118111 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9299 q selected
    | true =>
      simp only [d118111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9300 q selected
  have h2 (q : Pattern) (selected : d118112 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118113 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118119 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9300 q selected
    | true =>
      simp only [d118119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9301 q selected
  have h5 (q : Pattern) (selected : d118120 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118121 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118122 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9300 q selected
    | true =>
      simp only [d118124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9302 q selected
  have h9 (q : Pattern) (selected : d118125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118128 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118129 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9304 (p : Pattern) (selected : d118133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9300 q selected
    | true =>
      simp only [d118124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9302 q selected
  have h2 (q : Pattern) (selected : d118125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118132 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118133 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9305 (p : Pattern) (selected : d118139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118130 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9303 q selected
    | true =>
      simp only [d118130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118131 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118134 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9304 q selected
    | true =>
      simp only [d118134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118135 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118136 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118137 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118138 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118139 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9306 (p : Pattern) (selected : d118143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118134 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9304 q selected
    | true =>
      simp only [d118134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118135 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118140 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118141 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118142 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9307 (p : Pattern) (selected : d118159 p = 1) : d121753 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118096 q = 1) : d118096 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d118144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9305 q selected
    | true =>
      simp only [d118144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9306 q selected
  have h3 (q : Pattern) (selected : d118145 q = 1) : d121749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118145, d121749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118145, d121749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118155 q = 1) : d118155 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d118156 q = 1) : d121750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118156, d121750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118156, d121750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118157 q = 1) : d121751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118157, d121751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118157, d121751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118158 q = 1) : d121752 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118158, d121752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118158, d121752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118159 q = 1) : d121753 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118159, d121753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118159, d121753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9308 (p : Pattern) (selected : d118176 p = 1) : d121759 p = 1 := by
  have h0 (q : Pattern) (selected : d117858 q = 1) : d117858 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d117995 q = 1) : d121737 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d117995, d121737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9294 q selected
    | true =>
      simp only [d117995, d121737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9297 q selected
  have h2 (q : Pattern) (selected : d118013 q = 1) : d118013 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d118014 q = 1) : d121738 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118014, d121738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118014, d121738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d118015 q = 1) : d121739 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118015, d121739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118015, d121739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118016 q = 1) : d121740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118016, d121740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118016, d121740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118020 q = 1) : d121744 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118020, d121744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118020, d121744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9298 q selected
  have h8 (q : Pattern) (selected : d118022 q = 1) : d118022 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d118023 q = 1) : d121745 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118023, d121745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118023, d121745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118024 q = 1) : d121746 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118024, d121746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118024, d121746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d118025 q = 1) : d121747 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118025, d121747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118025, d121747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d118026 q = 1) : d121748 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118026, d121748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118026, d121748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118160 q = 1) : d121754 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118160, d121754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118160, d121754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9307 q selected
  have h14 (q : Pattern) (selected : d118171 q = 1) : d118171 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d118172 q = 1) : d121755 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118172, d121755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d118172, d121755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d118173 q = 1) : d121756 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118173, d121756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d118173, d121756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d118174 q = 1) : d121757 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118174, d121757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d118174, d121757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d118175 q = 1) : d121758 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118175, d121758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d118175, d121758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d118176 q = 1) : d121759 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d118176, d121759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118176, d121759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro9309 (p : Pattern) (selected : d118182 p = 1) : d121765 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118177 q = 1) : d121760 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d118177, d121760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118177, d121760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9308 q selected
  have h2 (q : Pattern) (selected : d118178 q = 1) : d121761 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d118178, d121761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118178, d121761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118179 q = 1) : d121762 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d118179, d121762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118179, d121762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118180 q = 1) : d121763 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d118180, d121763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118180, d121763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118181 q = 1) : d121764 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d118181, d121764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118181, d121764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118182 q = 1) : d121765 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d118182, d121765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118182, d121765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9310 (p : Pattern) (selected : d2199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2170 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro141 q selected
    | true =>
      simp only [d2170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro142 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2174 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro143 q selected
  have h3 (q : Pattern) (selected : d2175 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2186 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro144 q selected
    | true =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro145 q selected
  have h5 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h6 (q : Pattern) (selected : d2191 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2192 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2195 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro147 q selected
    | true =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d2196 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d2197 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2198 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2199 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h12 p selected
theorem eqIntro9311 (p : Pattern) (selected : d2217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d2186 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro144 q selected
    | true =>
      simp only [d2186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro145 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2190 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro146 q selected
  have h3 (q : Pattern) (selected : d2191 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2207 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro149 q selected
    | true =>
      simp only [d2207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro150 q selected
  have h5 (q : Pattern) (selected : d2209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h6 (q : Pattern) (selected : d2210 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2211 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2195 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro147 q selected
    | true =>
      simp only [d2195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h9 (q : Pattern) (selected : d2196 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h10 (q : Pattern) (selected : d2213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
    | true =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h11 (q : Pattern) (selected : d2214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h12 (q : Pattern) (selected : d2215 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d2216 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2217 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d2217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h14 p selected
theorem eqIntro9312 (p : Pattern) (selected : d118308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118300 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9310 q selected
    | true =>
      simp only [d118300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118302 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118303 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118304 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9311 q selected
    | true =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118305 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118306 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118308 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9313 (p : Pattern) (selected : d2229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2224 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro150 q selected
  have h2 (q : Pattern) (selected : d2209 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro151 q selected
  have h3 (q : Pattern) (selected : d2225 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
    | true =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2226 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2227 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2228 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2229 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro9314 (p : Pattern) (selected : d118313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118304 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9311 q selected
    | true =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118305 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118306 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118309 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9313 q selected
    | true =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118310 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118311 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118312 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118313 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9315 (p : Pattern) (selected : d10480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10476 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
  have h2 (q : Pattern) (selected : d10477 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2213 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro152 q selected
    | true =>
      simp only [d2213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2227 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10479 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10480 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9316 (p : Pattern) (selected : d118321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
    | true =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118319 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118320 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118321 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9317 (p : Pattern) (selected : d118326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118309 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9313 q selected
    | true =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118310 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118311 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118312 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118326 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro9318 (p : Pattern) (selected : d118332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118314 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9312 q selected
    | true =>
      simp only [d118314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9314 q selected
  have h2 (q : Pattern) (selected : d118315 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118316 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118322 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9314 q selected
    | true =>
      simp only [d118322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9316 q selected
  have h5 (q : Pattern) (selected : d118323 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118324 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118325 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9314 q selected
    | true =>
      simp only [d118327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9317 q selected
  have h9 (q : Pattern) (selected : d118328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118330 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118331 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118332 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9319 (p : Pattern) (selected : d118336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118327 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9314 q selected
    | true =>
      simp only [d118327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9317 q selected
  have h2 (q : Pattern) (selected : d118328 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118329 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118330 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118335 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118336 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9320 (p : Pattern) (selected : d118342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118333 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9318 q selected
    | true =>
      simp only [d118333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118334 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9319 q selected
    | true =>
      simp only [d118337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118339 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118340 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118341 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118342 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9321 (p : Pattern) (selected : d118346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9319 q selected
    | true =>
      simp only [d118337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118346 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9322 (p : Pattern) (selected : d118358 p = 1) : d121774 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118260 q = 1) : d118260 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d118269 q = 1) : d118269 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d118299 q = 1) : d118299 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d118347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9320 q selected
    | true =>
      simp only [d118347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9321 q selected
  have h5 (q : Pattern) (selected : d118348 q = 1) : d121770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118348, d121770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118348, d121770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118354 q = 1) : d118354 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d118355 q = 1) : d121771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118355, d121771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118355, d121771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118356 q = 1) : d121772 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118356, d121772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118356, d121772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118357 q = 1) : d121773 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118357, d121773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118357, d121773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118358 q = 1) : d121774 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118358, d121774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118358, d121774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro9323 (p : Pattern) (selected : d118373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118333 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9318 q selected
    | true =>
      simp only [d118333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118334 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9319 q selected
    | true =>
      simp only [d118337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118339 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118340 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118341 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118373 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9324 (p : Pattern) (selected : d118374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9319 q selected
    | true =>
      simp only [d118337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118374 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9325 (p : Pattern) (selected : d118383 p = 1) : d121779 p = 1 := by
  have h0 (q : Pattern) (selected : d118260 q = 1) : d118260 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118269 q = 1) : d118269 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d118299 q = 1) : d118299 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d118347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9320 q selected
    | true =>
      simp only [d118347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9321 q selected
  have h4 (q : Pattern) (selected : d118348 q = 1) : d121770 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118348, d121770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118348, d121770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118354 q = 1) : d118354 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d118355 q = 1) : d121771 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118355, d121771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118355, d121771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118356 q = 1) : d121772 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118356, d121772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118356, d121772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118357 q = 1) : d121773 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118357, d121773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118357, d121773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118364 q = 1) : d118364 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d118369 q = 1) : d118369 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d118372 q = 1) : d118372 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d118375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9323 q selected
    | true =>
      simp only [d118375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9324 q selected
  have h13 (q : Pattern) (selected : d118376 q = 1) : d121775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118376, d121775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118376, d121775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118379 q = 1) : d118379 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d118380 q = 1) : d121776 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118380, d121776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d118380, d121776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d118381 q = 1) : d121777 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118381, d121777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118381, d121777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d118382 q = 1) : d121778 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118382, d121778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118382, d121778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d118383 q = 1) : d121779 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118383, d121779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118383, d121779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro9326 (p : Pattern) (selected : d118408 p = 1) : d121786 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118372 q = 1) : d118372 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d118375 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9323 q selected
    | true =>
      simp only [d118375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9324 q selected
  have h3 (q : Pattern) (selected : d118376 q = 1) : d121775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118376, d121775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118376, d121775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118379 q = 1) : d118379 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d118380 q = 1) : d121776 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118380, d121776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118380, d121776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118406 q = 1) : d121784 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118406, d121784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118406, d121784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118407 q = 1) : d121785 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118407, d121785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118407, d121785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118408 q = 1) : d121786 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118408, d121786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118408, d121786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9327 (p : Pattern) (selected : d118489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118481 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9310 q selected
  have h2 (q : Pattern) (selected : d118300 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9310 q selected
    | true =>
      simp only [d118300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118482 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118301 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118483 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118484 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118485 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9311 q selected
  have h8 (q : Pattern) (selected : d118304 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9311 q selected
    | true =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118486 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118305 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118487 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118488 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118489 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9328 (p : Pattern) (selected : d118494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118485 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9311 q selected
  have h2 (q : Pattern) (selected : d118304 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9311 q selected
    | true =>
      simp only [d118304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118486 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118305 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118487 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118488 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9313 q selected
  have h8 (q : Pattern) (selected : d118309 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9313 q selected
    | true =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d118491 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118310 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d118492 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d118493 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d118493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d118494 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro9329 (p : Pattern) (selected : d118502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118498 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
  have h2 (q : Pattern) (selected : d118317 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9315 q selected
    | true =>
      simp only [d118317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118499 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118318 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118500 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118501 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118502 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9330 (p : Pattern) (selected : d118507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118490 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9313 q selected
  have h2 (q : Pattern) (selected : d118309 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9313 q selected
    | true =>
      simp only [d118309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118491 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118310 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118492 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d118492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118493 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d118493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118507 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d118507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro9331 (p : Pattern) (selected : d118513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9327 q selected
    | true =>
      simp only [d118495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9328 q selected
  have h2 (q : Pattern) (selected : d118496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118503 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9328 q selected
    | true =>
      simp only [d118503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9329 q selected
  have h5 (q : Pattern) (selected : d118504 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118505 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118506 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118508 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9328 q selected
    | true =>
      simp only [d118508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9330 q selected
  have h9 (q : Pattern) (selected : d118509 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118510 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118511 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d118512 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118513 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9332 (p : Pattern) (selected : d118517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118508 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d118508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9328 q selected
    | true =>
      simp only [d118508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9330 q selected
  have h2 (q : Pattern) (selected : d118509 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d118509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118510 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d118510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118511 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d118511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118516 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d118516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118517 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d118517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9333 (p : Pattern) (selected : d118523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118514 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9331 q selected
    | true =>
      simp only [d118514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118515 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118518 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9332 q selected
    | true =>
      simp only [d118518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118519 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118520 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118521 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d118522 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d118523 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9334 (p : Pattern) (selected : d118527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118518 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d118518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9332 q selected
    | true =>
      simp only [d118518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118519 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d118519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118524 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d118524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118525 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d118525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118526 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d118526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118527 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d118527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9335 (p : Pattern) (selected : d118543 p = 1) : d121796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118480 q = 1) : d118480 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d118528 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d118528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9333 q selected
    | true =>
      simp only [d118528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9334 q selected
  have h3 (q : Pattern) (selected : d118529 q = 1) : d121792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118529, d121792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118529, d121792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118539 q = 1) : d118539 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d118540 q = 1) : d121793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d118540, d121793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118540, d121793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118541 q = 1) : d121794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d118541, d121794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118541, d121794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118542 q = 1) : d121795 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d118542, d121795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118542, d121795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d118543 q = 1) : d121796 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d118543, d121796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118543, d121796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9336 (p : Pattern) (selected : d118560 p = 1) : d121802 p = 1 := by
  have h0 (q : Pattern) (selected : d118252 q = 1) : d118252 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118384 q = 1) : d121780 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118384, d121780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9322 q selected
    | true =>
      simp only [d118384, d121780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9325 q selected
  have h2 (q : Pattern) (selected : d118402 q = 1) : d118402 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d118403 q = 1) : d121781 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118403, d121781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118403, d121781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d118404 q = 1) : d121782 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118404, d121782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118404, d121782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118405 q = 1) : d121783 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118405, d121783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118405, d121783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118409 q = 1) : d121787 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118409, d121787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118409, d121787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9326 q selected
  have h8 (q : Pattern) (selected : d118411 q = 1) : d118411 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d118412 q = 1) : d121788 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118412, d121788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d118412, d121788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118413 q = 1) : d121789 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118413, d121789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d118413, d121789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d118414 q = 1) : d121790 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118414, d121790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118414, d121790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d118415 q = 1) : d121791 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118415, d121791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118415, d121791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118544 q = 1) : d121797 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d118544, d121797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118544, d121797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9335 q selected
  have h14 (q : Pattern) (selected : d118555 q = 1) : d118555 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d118556 q = 1) : d121798 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d118556, d121798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d118556, d121798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d118557 q = 1) : d121799 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d118557, d121799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d118557, d121799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d118558 q = 1) : d121800 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d118558, d121800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d118558, d121800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d118559 q = 1) : d121801 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d118559, d121801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d118559, d121801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d118560 q = 1) : d121802 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d118560, d121802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d118560, d121802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro9337 (p : Pattern) (selected : d118566 p = 1) : d121808 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118561 q = 1) : d121803 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d118561, d121803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118561, d121803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9336 q selected
  have h2 (q : Pattern) (selected : d118562 q = 1) : d121804 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d118562, d121804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118562, d121804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d118563 q = 1) : d121805 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d118563, d121805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118563, d121805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d118564 q = 1) : d121806 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d118564, d121806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118564, d121806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d118565 q = 1) : d121807 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d118565, d121807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118565, d121807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d118566 q = 1) : d121808 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d118566, d121808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118566, d121808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9338 (p : Pattern) (selected : d118572 p = 1) : d121814 p = 1 := by
  have h0 (q : Pattern) (selected : d117157 q = 1) : d121643 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d117157, d121643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9221 q selected
    | true =>
      simp only [d117157, d121643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9235 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d117450 q = 1) : d121683 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d117450, d121683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117450, d121683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9256 q selected
  have h3 (q : Pattern) (selected : d117451 q = 1) : d121684 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d117451, d121684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d117451, d121684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d117790 q = 1) : d121724 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d117790, d121724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117790, d121724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9281 q selected
  have h5 (q : Pattern) (selected : d117791 q = 1) : d121725 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d117791, d121725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d117791, d121725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d117792 q = 1) : d121726 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d117792, d121726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d117792, d121726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d118183 q = 1) : d121766 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d118183, d121766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118183, d121766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9309 q selected
  have h8 (q : Pattern) (selected : d118184 q = 1) : d121767 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d118184, d121767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118184, d121767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d118185 q = 1) : d121768 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d118185, d121768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118185, d121768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d118186 q = 1) : d121769 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d118186, d121769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d118186, d121769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d118567 q = 1) : d121809 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d118567, d121809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118567, d121809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9337 q selected
  have h12 (q : Pattern) (selected : d118568 q = 1) : d121810 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d118568, d121810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118568, d121810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d118569 q = 1) : d121811 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d118569, d121811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118569, d121811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d118570 q = 1) : d121812 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d118570, d121812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118570, d121812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d118571 q = 1) : d121813 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d118571, d121813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d118571, d121813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d118572 q = 1) : d121814 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d118572, d121814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d118572, d121814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro9339 (p : Pattern) (selected : d118578 p = 1) : d121820 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118573 q = 1) : d121815 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d118573, d121815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9338 q selected
    | true =>
      simp only [d118573, d121815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118574 q = 1) : d121816 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d118574, d121816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118574, d121816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118575 q = 1) : d121817 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d118575, d121817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118575, d121817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118576 q = 1) : d121818 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d118576, d121818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118576, d121818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118577 q = 1) : d121819 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d118577, d121819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118577, d121819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118578 q = 1) : d121820 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d118578, d121820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118578, d121820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9340 (p : Pattern) (selected : d118584 p = 1) : d121826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118579 q = 1) : d121821 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d118579, d121821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9339 q selected
    | true =>
      simp only [d118579, d121821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118580 q = 1) : d121822 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d118580, d121822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118580, d121822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118581 q = 1) : d121823 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d118581, d121823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118581, d121823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118582 q = 1) : d121824 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d118582, d121824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118582, d121824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118583 q = 1) : d121825 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d118583, d121825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118583, d121825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118584 q = 1) : d121826 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d118584, d121826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118584, d121826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9341 (p : Pattern) (selected : d118590 p = 1) : d121832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118585 q = 1) : d121827 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d118585, d121827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9340 q selected
    | true =>
      simp only [d118585, d121827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118586 q = 1) : d121828 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d118586, d121828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118586, d121828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118587 q = 1) : d121829 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d118587, d121829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118587, d121829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118588 q = 1) : d121830 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d118588, d121830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118588, d121830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118589 q = 1) : d121831 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d118589, d121831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118589, d121831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118590 q = 1) : d121832 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d118590, d121832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118590, d121832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9342 (p : Pattern) (selected : d118596 p = 1) : d121838 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118591 q = 1) : d121833 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d118591, d121833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9341 q selected
    | true =>
      simp only [d118591, d121833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118592 q = 1) : d121834 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d118592, d121834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118592, d121834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118593 q = 1) : d121835 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d118593, d121835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118593, d121835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118594 q = 1) : d121836 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d118594, d121836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118594, d121836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118595 q = 1) : d121837 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d118595, d121837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118595, d121837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118596 q = 1) : d121838 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d118596, d121838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118596, d121838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9343 (p : Pattern) (selected : d118602 p = 1) : d121844 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118597 q = 1) : d121839 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d118597, d121839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9342 q selected
    | true =>
      simp only [d118597, d121839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118598 q = 1) : d121840 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d118598, d121840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118598, d121840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118599 q = 1) : d121841 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d118599, d121841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118599, d121841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118600 q = 1) : d121842 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d118600, d121842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118600, d121842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118601 q = 1) : d121843 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d118601, d121843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118601, d121843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118602 q = 1) : d121844 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d118602, d121844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118602, d121844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9344 (p : Pattern) (selected : d118608 p = 1) : d121850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118603 q = 1) : d121845 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d118603, d121845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9343 q selected
    | true =>
      simp only [d118603, d121845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118604 q = 1) : d121846 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d118604, d121846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118604, d121846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118605 q = 1) : d121847 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d118605, d121847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118605, d121847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118606 q = 1) : d121848 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d118606, d121848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118606, d121848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118607 q = 1) : d121849 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d118607, d121849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118607, d121849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118608 q = 1) : d121850 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d118608, d121850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118608, d121850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9345 (p : Pattern) (selected : d118614 p = 1) : d121856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d118609 q = 1) : d121851 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d118609, d121851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9344 q selected
    | true =>
      simp only [d118609, d121851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118610 q = 1) : d121852 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d118610, d121852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d118610, d121852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d118611 q = 1) : d121853 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d118611, d121853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d118611, d121853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d118612 q = 1) : d121854 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d118612, d121854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d118612, d121854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d118613 q = 1) : d121855 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d118613, d121855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d118613, d121855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d118614 q = 1) : d121856 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d118614, d121856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d118614, d121856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9346 (p : Pattern) (selected : d13981 p = 0) : d122308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d139 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d140 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d141 q = 0) : d51992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d141, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142 q = 0) : d51993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d142, d51993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13980 q = 0) : d122307 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13980, d122307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13980, d122307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d27 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d28 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d29 q = 0) : d51881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d13981 q = 0) : d122308 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13981, d122308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13981, d122308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9347 (p : Pattern) (selected : d13987 p = 0) : d122314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13982 q = 0) : d122309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9346 q selected
    | true =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h2 (q : Pattern) (selected : d13983 q = 0) : d122310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13984 q = 0) : d122311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d31 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d13985 q = 0) : d122312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, d122312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13985, d122312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d34 q = 0) : d51886 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d13986 q = 0) : d122313 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13986, d122313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13986, d122313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d13987 q = 0) : d122314 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13987, d122314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d13987, d122314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9348 (p : Pattern) (selected : d13993 p = 0) : d122320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13988 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9347 q selected
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13989 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13990 q = 0) : d122317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13991 q = 0) : d122318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13992 q = 0) : d122319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, d122319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13992, d122319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13993 q = 0) : d122320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13993, d122320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13993, d122320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9349 (p : Pattern) (selected : d13999 p = 0) : d122326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117 q = 0) : d51969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 0) : d51970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 0) : d51971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 0) : d51972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 0) : d51976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 0) : d51977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 0) : d51978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13994 q = 0) : d122321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9348 q selected
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h9 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d13995 q = 0) : d122322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13995, d122322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13995, d122322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13996 q = 0) : d122323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13996, d122323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13996, d122323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13997 q = 0) : d122324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13997, d122324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13997, d122324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13998 q = 0) : d122325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13998, d122325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13998, d122325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d13999 q = 0) : d122326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13999, d122326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13999, d122326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro9350 (p : Pattern) (selected : d14000 p = 0) : d122327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13988 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9347 q selected
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13989 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13990 q = 0) : d122317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13991 q = 0) : d122318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d13992 q = 0) : d122319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, d122319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13992, d122319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14000 q = 0) : d122327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14000, d122327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14000, d122327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9351 (p : Pattern) (selected : d14006 p = 0) : d122333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117 q = 0) : d51969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 0) : d51970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 0) : d51971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 0) : d51972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 0) : d51976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 0) : d51977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 0) : d51978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13994 q = 0) : d122321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9348 q selected
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h9 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d13995 q = 0) : d122322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13995, d122322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13995, d122322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d13996 q = 0) : d122323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13996, d122323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d13996, d122323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d13997 q = 0) : d122324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13997, d122324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d13997, d122324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d13998 q = 0) : d122325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13998, d122325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d13998, d122325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195 q = 0) : d52015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d196 q = 0) : d52016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d197 q = 0) : d52017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d198 q = 0) : d52018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d200 q = 0) : d52020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d201 q = 0) : d52021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d202 q = 0) : d52022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d14001 q = 0) : d122328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9350 q selected
    | true =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h24 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d14002 q = 0) : d122329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14002, d122329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d14002, d122329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d14003 q = 0) : d122330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14003, d122330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d14003, d122330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d14004 q = 0) : d122331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14004, d122331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d14004, d122331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d14005 q = 0) : d122332 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14005, d122332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d14005, d122332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d14006 q = 0) : d122333 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14006, d122333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d14006, d122333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro9352 (p : Pattern) (selected : d14013 p = 0) : d122340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14001 q = 0) : d122328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9350 q selected
    | true =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h2 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14002 q = 0) : d122329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14002, d122329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14002, d122329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14003 q = 0) : d122330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14003, d122330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14003, d122330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14011 q = 0) : d122338 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14011, d122338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14011, d122338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14012 q = 0) : d122339 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14012, d122339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14012, d122339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14013 q = 0) : d122340 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14013, d122340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14013, d122340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9353 (p : Pattern) (selected : d14020 p = 0) : d122347 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d226 q = 0) : d52044 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
  have h2 (q : Pattern) (selected : d139 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro205 q selected
    | true =>
      simp only [d139, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227 q = 0) : d52045 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d140 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d140, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d228 q = 0) : d52046 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d228, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d229 q = 0) : d52047 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d229, d52047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14019 q = 0) : d122346 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14019, d122346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14019, d122346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d66 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h9 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d67 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d68 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d69 q = 0) : d51921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d70 q = 0) : d51922 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14020 q = 0) : d122347 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14020, d122347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14020, d122347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9354 (p : Pattern) (selected : d14026 p = 0) : d122353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14021 q = 0) : d122348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9353 q selected
    | true =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h2 (q : Pattern) (selected : d14022 q = 0) : d122349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14023 q = 0) : d122350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d72 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d74 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14024 q = 0) : d122351 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, d122351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14024, d122351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d75 q = 0) : d51927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14025 q = 0) : d122352 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14025, d122352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14025, d122352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14026 q = 0) : d122353 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14026, d122353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14026, d122353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9355 (p : Pattern) (selected : d14032 p = 0) : d122359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14027 q = 0) : d122354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d122354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9354 q selected
    | true =>
      simp only [d14027, d122354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14028 q = 0) : d122355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d122355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14028, d122355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro196 q selected
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d79 q = 0) : d51931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14029 q = 0) : d122356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14029, d122356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14029, d122356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14030 q = 0) : d122357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14030, d122357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14030, d122357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14031 q = 0) : d122358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14031, d122358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14031, d122358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14032 q = 0) : d122359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14032, d122359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14032, d122359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9356 (p : Pattern) (selected : d14038 p = 0) : d122365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14033 q = 0) : d122360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, d122360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9355 q selected
    | true =>
      simp only [d14033, d122360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
  have h2 (q : Pattern) (selected : d263 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
    | true =>
      simp only [d263, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14034 q = 0) : d122361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14034, d122361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14034, d122361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d84 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85 q = 0) : d51937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14035 q = 0) : d122362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14035, d122362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14035, d122362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14036 q = 0) : d122363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14036, d122363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14036, d122363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14037 q = 0) : d122364 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14037, d122364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14037, d122364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14038 q = 0) : d122365 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14038, d122365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14038, d122365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9357 (p : Pattern) (selected : d14044 p = 0) : d122371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105 q = 0) : d51957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
  have h2 (q : Pattern) (selected : d106 q = 0) : d51958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d112 q = 0) : d51964 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h4 (q : Pattern) (selected : d113 q = 0) : d51965 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d114 q = 0) : d51966 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14007 q = 0) : d122334 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14007, d122334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9349 q selected
    | true =>
      simp only [d14007, d122334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9351 q selected
  have h7 (q : Pattern) (selected : d214 q = 0) : d52032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14008 q = 0) : d122335 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14008, d122335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14008, d122335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14009 q = 0) : d122336 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14009, d122336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14009, d122336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14010 q = 0) : d122337 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14010, d122337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14010, d122337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14014 q = 0) : d122341 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14014, d122341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14014, d122341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9352 q selected
  have h12 (q : Pattern) (selected : d14015 q = 0) : d122342 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14015, d122342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d14015, d122342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14016 q = 0) : d122343 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14016, d122343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14016, d122343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14017 q = 0) : d122344 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14017, d122344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d14017, d122344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14018 q = 0) : d122345 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d14018, d122345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14018, d122345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14039 q = 0) : d122366 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14039, d122366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14039, d122366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9356 q selected
  have h17 (q : Pattern) (selected : d14040 q = 0) : d122367 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14040, d122367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d14040, d122367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d14041 q = 0) : d122368 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14041, d122368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d14041, d122368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d14042 q = 0) : d122369 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14042, d122369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d14042, d122369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d14043 q = 0) : d122370 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d14043, d122370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d14043, d122370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d14044 q = 0) : d122371 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d14044, d122371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d14044, d122371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro9358 (p : Pattern) (selected : d14054 p = 0) : d122381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13994 q = 0) : d122321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9348 q selected
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d14050 q = 0) : d122377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14051 q = 0) : d122378 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14052 q = 0) : d122379 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14053 q = 0) : d122380 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14054 q = 0) : d122381 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, d122381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14054, d122381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9359 (p : Pattern) (selected : d14061 p = 0) : d122388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13994 q = 0) : d122321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9348 q selected
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d14050 q = 0) : d122377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14051 q = 0) : d122378 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14052 q = 0) : d122379 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14053 q = 0) : d122380 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14001 q = 0) : d122328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9350 q selected
    | true =>
      simp only [d14001, d122328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h7 (q : Pattern) (selected : d14057 q = 0) : d122384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d122384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14057, d122384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14058 q = 0) : d122385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d122385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14058, d122385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14059 q = 0) : d122386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d122386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14059, d122386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14060 q = 0) : d122387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d122387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14060, d122387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14061 q = 0) : d122388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, d122388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14061, d122388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9360 (p : Pattern) (selected : d14066 p = 0) : d122393 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13988 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9347 q selected
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13989 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13990 q = 0) : d122317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13991 q = 0) : d122318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14065 q = 0) : d122392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, d122392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14065, d122392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14066 q = 0) : d122393 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14066, d122393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14066, d122393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9361 (p : Pattern) (selected : d14073 p = 0) : d122400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13988 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9347 q selected
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13989 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13990 q = 0) : d122317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14071 q = 0) : d122398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, d122398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14071, d122398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14072 q = 0) : d122399 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, d122399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14072, d122399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14073 q = 0) : d122400 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14073, d122400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14073, d122400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9362 (p : Pattern) (selected : d14079 p = 0) : d122406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d319 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d320 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d321 q = 0) : d52120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d322 q = 0) : d52121 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14077 q = 0) : d122404 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, d122404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14077, d122404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12493 q = 0) : d112927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d12494 q = 0) : d112928 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14078 q = 0) : d122405 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14078, d122405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14078, d122405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d14079 q = 0) : d122406 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14079, d122406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14079, d122406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9363 (p : Pattern) (selected : d14085 p = 0) : d122412 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14080 q = 0) : d122407 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, d122407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9362 q selected
    | true =>
      simp only [d14080, d122407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9346 q selected
  have h2 (q : Pattern) (selected : d14081 q = 0) : d122408 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, d122408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14081, d122408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14082 q = 0) : d122409 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d122409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14082, d122409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13982 q = 0) : d122309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9346 q selected
    | true =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h5 (q : Pattern) (selected : d13983 q = 0) : d122310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13984 q = 0) : d122311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14083 q = 0) : d122410 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, d122410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14083, d122410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d31 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d33 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13985 q = 0) : d122312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, d122312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13985, d122312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14084 q = 0) : d122411 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14084, d122411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14084, d122411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d14085 q = 0) : d122412 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14085, d122412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14085, d122412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9364 (p : Pattern) (selected : d14091 p = 0) : d122418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14086 q = 0) : d122413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, d122413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9363 q selected
    | true =>
      simp only [d14086, d122413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14087 q = 0) : d122414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, d122414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14087, d122414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13988 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9347 q selected
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13989 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14088 q = 0) : d122415 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, d122415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14088, d122415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14089 q = 0) : d122416 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, d122416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14089, d122416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14090 q = 0) : d122417 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, d122417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14090, d122417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14091 q = 0) : d122418 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14091, d122418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14091, d122418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9365 (p : Pattern) (selected : d14094 p = 0) : d122308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d350 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352 q = 0) : d51992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352, d51992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d353 q = 0) : d51993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d353, d51993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d353, d51993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14093 q = 0) : d122307 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14093, d122307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14093, d122307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d172 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d173 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d173, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d174 q = 0) : d51881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d174, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d14094 q = 0) : d122308 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14094, d122308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14094, d122308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9366 (p : Pattern) (selected : d14100 p = 0) : d122314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14095 q = 0) : d122309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14095, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9365 q selected
    | true =>
      simp only [d14095, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
  have h2 (q : Pattern) (selected : d14096 q = 0) : d122310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14096, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14096, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14097 q = 0) : d122311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14097, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14097, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
    | true =>
      simp only [d176, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d178 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14098 q = 0) : d122312 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14098, d122312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14098, d122312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d179 q = 0) : d51886 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d179, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d179, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14099 q = 0) : d122313 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14099, d122313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14099, d122313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14100 q = 0) : d122314 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14100, d122314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14100, d122314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9367 (p : Pattern) (selected : d14106 p = 0) : d122320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14101 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14101, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9366 q selected
    | true =>
      simp only [d14101, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14102 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14102, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14102, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14103 q = 0) : d122317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14103, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14103, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14104 q = 0) : d122318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14104, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14104, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14105 q = 0) : d122319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14105, d122319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14105, d122319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14106 q = 0) : d122320 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14106, d122320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14106, d122320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9368 (p : Pattern) (selected : d14112 p = 0) : d122424 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13988 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9347 q selected
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13989 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14109 q = 0) : d122421 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, d122421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14109, d122421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14110 q = 0) : d122422 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, d122422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14110, d122422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14111 q = 0) : d122423 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, d122423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14111, d122423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14112 q = 0) : d122424 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14112, d122424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14112, d122424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9369 (p : Pattern) (selected : d14118 p = 0) : d122430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14067 q = 0) : d122394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, d122394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9360 q selected
    | true =>
      simp only [d14067, d122394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d14068 q = 0) : d122395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, d122395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14068, d122395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14069 q = 0) : d122396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, d122396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14069, d122396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14070 q = 0) : d122397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, d122397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14070, d122397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14074 q = 0) : d122401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, d122401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9361 q selected
    | true =>
      simp only [d14074, d122401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d14075 q = 0) : d122402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, d122402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14075, d122402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14076 q = 0) : d122403 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, d122403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14076, d122403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14092 q = 0) : d122419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, d122419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9364 q selected
    | true =>
      simp only [d14092, d122419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9348 q selected
  have h9 (q : Pattern) (selected : d14107 q = 0) : d122321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14107, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9367 q selected
    | true =>
      simp only [d14107, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d14108 q = 0) : d122420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14108, d122420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14108, d122420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14113 q = 0) : d122425 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, d122425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9368 q selected
    | true =>
      simp only [d14113, d122425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d14114 q = 0) : d122426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, d122426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d14114, d122426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14115 q = 0) : d122427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14115, d122427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14115, d122427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14116 q = 0) : d122428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14116, d122428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14116, d122428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14117 q = 0) : d122429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14117, d122429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14117, d122429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14118 q = 0) : d122430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14118, d122430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14118, d122430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro9370 (p : Pattern) (selected : d14119 p = 0) : d122431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13988 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9347 q selected
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13989 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13990 q = 0) : d122317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13991 q = 0) : d122318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13991, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14065 q = 0) : d122392 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, d122392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14065, d122392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14119 q = 0) : d122431 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14119, d122431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14119, d122431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9371 (p : Pattern) (selected : d14124 p = 0) : d122436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13988 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9347 q selected
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13989 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d13990 q = 0) : d122317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d13990, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14071 q = 0) : d122398 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, d122398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14071, d122398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14072 q = 0) : d122399 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, d122399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14072, d122399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14124 q = 0) : d122436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14124, d122436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14124, d122436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9372 (p : Pattern) (selected : d14128 p = 0) : d122440 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14086 q = 0) : d122413 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, d122413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9363 q selected
    | true =>
      simp only [d14086, d122413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14087 q = 0) : d122414 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, d122414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14087, d122414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13988 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9347 q selected
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d13989 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14088 q = 0) : d122415 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, d122415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14088, d122415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14089 q = 0) : d122416 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, d122416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14089, d122416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14090 q = 0) : d122417 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, d122417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14090, d122417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14128 q = 0) : d122440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14128, d122440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14128, d122440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9373 (p : Pattern) (selected : d14130 p = 0) : d122327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14101 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14101, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9366 q selected
    | true =>
      simp only [d14101, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14102 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14102, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14102, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14103 q = 0) : d122317 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14103, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14103, d122317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14104 q = 0) : d122318 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14104, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14104, d122318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14105 q = 0) : d122319 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14105, d122319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14105, d122319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14130 q = 0) : d122327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14130, d122327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14130, d122327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9374 (p : Pattern) (selected : d14133 p = 0) : d122443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13988 q = 0) : d122315 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9347 q selected
    | true =>
      simp only [d13988, d122315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d13989 q = 0) : d122316 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13989, d122316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14109 q = 0) : d122421 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, d122421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14109, d122421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14110 q = 0) : d122422 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, d122422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14110, d122422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14111 q = 0) : d122423 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, d122423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14111, d122423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14133 q = 0) : d122443 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14133, d122443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14133, d122443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9375 (p : Pattern) (selected : d14139 p = 0) : d122449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14067 q = 0) : d122394 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, d122394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9360 q selected
    | true =>
      simp only [d14067, d122394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d14068 q = 0) : d122395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, d122395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14068, d122395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14069 q = 0) : d122396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, d122396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14069, d122396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14070 q = 0) : d122397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, d122397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14070, d122397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14074 q = 0) : d122401 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, d122401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9361 q selected
    | true =>
      simp only [d14074, d122401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d14075 q = 0) : d122402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, d122402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14075, d122402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14076 q = 0) : d122403 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, d122403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14076, d122403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14092 q = 0) : d122419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, d122419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9364 q selected
    | true =>
      simp only [d14092, d122419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9348 q selected
  have h9 (q : Pattern) (selected : d14107 q = 0) : d122321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14107, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9367 q selected
    | true =>
      simp only [d14107, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d14108 q = 0) : d122420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14108, d122420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14108, d122420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14113 q = 0) : d122425 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, d122425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9368 q selected
    | true =>
      simp only [d14113, d122425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d14114 q = 0) : d122426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, d122426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d14114, d122426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14115 q = 0) : d122427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14115, d122427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14115, d122427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14116 q = 0) : d122428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14116, d122428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14116, d122428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14117 q = 0) : d122429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14117, d122429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14117, d122429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14120 q = 0) : d122432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14120, d122432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9370 q selected
    | true =>
      simp only [d14120, d122432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
  have h17 (q : Pattern) (selected : d14121 q = 0) : d122433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14121, d122433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14121, d122433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d14122 q = 0) : d122434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14122, d122434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d14122, d122434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d14123 q = 0) : d122435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14123, d122435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14123, d122435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d14125 q = 0) : d122437 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14125, d122437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9371 q selected
    | true =>
      simp only [d14125, d122437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
  have h21 (q : Pattern) (selected : d14126 q = 0) : d122438 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14126, d122438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14126, d122438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d14127 q = 0) : d122439 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14127, d122439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d14127, d122439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d14129 q = 0) : d122441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, d122441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9372 q selected
    | true =>
      simp only [d14129, d122441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9350 q selected
  have h24 (q : Pattern) (selected : d14131 q = 0) : d122328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14131, d122328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9373 q selected
    | true =>
      simp only [d14131, d122328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h25 (q : Pattern) (selected : d14132 q = 0) : d122442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14132, d122442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d14132, d122442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d14134 q = 0) : d122444 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, d122444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9374 q selected
    | true =>
      simp only [d14134, d122444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d14135 q = 0) : d122445 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, d122445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d14135, d122445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d14136 q = 0) : d122446 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14136, d122446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d14136, d122446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d14137 q = 0) : d122447 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14137, d122447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d14137, d122447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d14138 q = 0) : d122448 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14138, d122448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d14138, d122448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d14139 q = 0) : d122449 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14139, d122449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d14139, d122449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro9376 (p : Pattern) (selected : d14141 p = 0) : d122451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13994 q = 0) : d122321 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9348 q selected
    | true =>
      simp only [d13994, d122321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d14050 q = 0) : d122377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14050, d122377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14051 q = 0) : d122378 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14051, d122378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14052 q = 0) : d122379 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14052, d122379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14053 q = 0) : d122380 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14053, d122380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d100 q = 0) : d51952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d101 q = 0) : d51953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d102 q = 0) : d51954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103 q = 0) : d51955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14141 q = 0) : d122451 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14141, d122451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14141, d122451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9377 (p : Pattern) (selected : d14148 p = 0) : d122458 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14129 q = 0) : d122441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, d122441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9372 q selected
    | true =>
      simp only [d14129, d122441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9350 q selected
  have h2 (q : Pattern) (selected : d14131 q = 0) : d122328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14131, d122328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9373 q selected
    | true =>
      simp only [d14131, d122328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h3 (q : Pattern) (selected : d14132 q = 0) : d122442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14132, d122442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14132, d122442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14134 q = 0) : d122444 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, d122444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9374 q selected
    | true =>
      simp only [d14134, d122444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14135 q = 0) : d122445 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, d122445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14135, d122445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14136 q = 0) : d122446 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14136, d122446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14136, d122446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14146 q = 0) : d122456 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14146, d122456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14146, d122456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14147 q = 0) : d122457 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14147, d122457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14147, d122457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14148 q = 0) : d122458 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14148, d122458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14148, d122458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9378 (p : Pattern) (selected : d14156 p = 0) : d122466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d412 q = 0) : d52178 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
  have h2 (q : Pattern) (selected : d319 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d413 q = 0) : d52179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d320 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d414 q = 0) : d52180 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d415 q = 0) : d52181 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14154 q = 0) : d122464 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14154, d122464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14154, d122464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12599 q = 0) : d113007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
  have h9 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d12600 q = 0) : d113008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d12601 q = 0) : d113009 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d12602 q = 0) : d113010 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14155 q = 0) : d122465 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14155, d122465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d14155, d122465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14156 q = 0) : d122466 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14156, d122466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14156, d122466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9379 (p : Pattern) (selected : d14162 p = 0) : d122472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14157 q = 0) : d122467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, d122467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9378 q selected
    | true =>
      simp only [d14157, d122467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9353 q selected
  have h2 (q : Pattern) (selected : d14158 q = 0) : d122468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, d122468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14158, d122468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14159 q = 0) : d122469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d122469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14159, d122469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14021 q = 0) : d122348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9353 q selected
    | true =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h5 (q : Pattern) (selected : d14022 q = 0) : d122349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14023 q = 0) : d122350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14160 q = 0) : d122470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, d122470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14160, d122470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d72 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d73 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d74 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14024 q = 0) : d122351 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, d122351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14024, d122351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14161 q = 0) : d122471 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14161, d122471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14161, d122471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d14162 q = 0) : d122472 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14162, d122472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14162, d122472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro9380 (p : Pattern) (selected : d14168 p = 0) : d122478 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14163 q = 0) : d122473 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14163, d122473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9379 q selected
    | true =>
      simp only [d14163, d122473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14164 q = 0) : d122474 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14164, d122474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14164, d122474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14027 q = 0) : d122354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d122354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9354 q selected
    | true =>
      simp only [d14027, d122354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14028 q = 0) : d122355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d122355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14028, d122355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14165 q = 0) : d122475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14165, d122475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14165, d122475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14166 q = 0) : d122476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14166, d122476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14166, d122476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14167 q = 0) : d122477 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14167, d122477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14167, d122477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14168 q = 0) : d122478 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14168, d122478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14168, d122478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9381 (p : Pattern) (selected : d14171 p = 0) : d122347 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d431 q = 0) : d52044 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, d52044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
  have h2 (q : Pattern) (selected : d350 q = 0) : d51990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro240 q selected
    | true =>
      simp only [d350, d51990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d432 q = 0) : d52045 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d432, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d432, d52045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351 q = 0) : d51991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351, d51991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d433 q = 0) : d52046 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d433, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d433, d52046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d434 q = 0) : d52047 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d434, d52047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d434, d52047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14170 q = 0) : d122346 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14170, d122346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14170, d122346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d245 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
  have h9 (q : Pattern) (selected : d170 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro210 q selected
    | true =>
      simp only [d170, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d246 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d246, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d171 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d171, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d247 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d247, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d248 q = 0) : d51921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d248, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d249 q = 0) : d51922 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d249, d51922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d249, d51922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14171 q = 0) : d122347 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14171, d122347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14171, d122347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9382 (p : Pattern) (selected : d14177 p = 0) : d122353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14172 q = 0) : d122348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14172, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9381 q selected
    | true =>
      simp only [d14172, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h2 (q : Pattern) (selected : d14173 q = 0) : d122349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14173, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14173, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14174 q = 0) : d122350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14174, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14174, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d251 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
    | true =>
      simp only [d251, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d252 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14175 q = 0) : d122351 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14175, d122351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14175, d122351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254 q = 0) : d51927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14176 q = 0) : d122352 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14176, d122352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14176, d122352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14177 q = 0) : d122353 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14177, d122353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14177, d122353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9383 (p : Pattern) (selected : d14183 p = 0) : d122359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14178 q = 0) : d122354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14178, d122354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9382 q selected
    | true =>
      simp only [d14178, d122354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14179 q = 0) : d122355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14179, d122355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14179, d122355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d257 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro226 q selected
    | true =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d258 q = 0) : d51931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d258, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d258, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14180 q = 0) : d122356 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14180, d122356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14180, d122356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14181 q = 0) : d122357 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14181, d122357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14181, d122357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14182 q = 0) : d122358 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14182, d122358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14182, d122358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14183 q = 0) : d122359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14183, d122359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14183, d122359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9384 (p : Pattern) (selected : d14189 p = 0) : d122484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14027 q = 0) : d122354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d122354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9354 q selected
    | true =>
      simp only [d14027, d122354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14028 q = 0) : d122355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d122355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14028, d122355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14186 q = 0) : d122481 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14186, d122481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14186, d122481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14187 q = 0) : d122482 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14187, d122482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14187, d122482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14188 q = 0) : d122483 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14188, d122483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14188, d122483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14189 q = 0) : d122484 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14189, d122484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14189, d122484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9385 (p : Pattern) (selected : d14195 p = 0) : d122490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14169 q = 0) : d122479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14169, d122479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9380 q selected
    | true =>
      simp only [d14169, d122479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9355 q selected
  have h2 (q : Pattern) (selected : d14184 q = 0) : d122360 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14184, d122360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9383 q selected
    | true =>
      simp only [d14184, d122360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
  have h3 (q : Pattern) (selected : d14185 q = 0) : d122480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14185, d122480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14185, d122480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14190 q = 0) : d122485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14190, d122485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9384 q selected
    | true =>
      simp only [d14190, d122485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14191 q = 0) : d122486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14191, d122486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14191, d122486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14192 q = 0) : d122487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14192, d122487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14192, d122487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14193 q = 0) : d122488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14193, d122488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14193, d122488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14194 q = 0) : d122489 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14194, d122489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14194, d122489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14195 q = 0) : d122490 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14195, d122490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14195, d122490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9386 (p : Pattern) (selected : d14201 p = 0) : d122496 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14055 q = 0) : d122382 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14055, d122382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14055, d122382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9358 q selected
  have h2 (q : Pattern) (selected : d14056 q = 0) : d122383 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14056, d122383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14056, d122383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14062 q = 0) : d122389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, d122389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9358 q selected
    | true =>
      simp only [d14062, d122389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9359 q selected
  have h4 (q : Pattern) (selected : d14063 q = 0) : d122390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, d122390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14063, d122390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14064 q = 0) : d122391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14064, d122391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14064, d122391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14140 q = 0) : d122450 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14140, d122450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9369 q selected
    | true =>
      simp only [d14140, d122450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9375 q selected
  have h7 (q : Pattern) (selected : d14142 q = 0) : d122452 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14142, d122452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9376 q selected
    | true =>
      simp only [d14142, d122452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h8 (q : Pattern) (selected : d14143 q = 0) : d122453 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14143, d122453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14143, d122453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14144 q = 0) : d122454 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14144, d122454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14144, d122454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14145 q = 0) : d122455 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14145, d122455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14145, d122455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14149 q = 0) : d122459 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14149, d122459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14149, d122459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9377 q selected
  have h12 (q : Pattern) (selected : d407 q = 0) : d52173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro252 q selected
  have h13 (q : Pattern) (selected : d14150 q = 0) : d122460 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14150, d122460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d14150, d122460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14151 q = 0) : d122461 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14151, d122461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d14151, d122461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14152 q = 0) : d122462 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14152, d122462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d14152, d122462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d14153 q = 0) : d122463 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d14153, d122463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14153, d122463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d14196 q = 0) : d122491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14196, d122491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14196, d122491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9385 q selected
  have h18 (q : Pattern) (selected : d463 q = 0) : d52210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro260 q selected
  have h19 (q : Pattern) (selected : d14197 q = 0) : d122492 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14197, d122492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d14197, d122492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d14198 q = 0) : d122493 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14198, d122493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d14198, d122493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d14199 q = 0) : d122494 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14199, d122494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d14199, d122494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d14200 q = 0) : d122495 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d14200, d122495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d14200, d122495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d14201 q = 0) : d122496 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d14201, d122496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d14201, d122496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro9387 (p : Pattern) (selected : d14207 p = 0) : d122502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96 q = 0) : d51948 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro199 q selected
  have h2 (q : Pattern) (selected : d97 q = 0) : d51949 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 0) : d51950 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 0) : d51951 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14045 q = 0) : d122372 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d14045, d122372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14045, d122372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9357 q selected
  have h6 (q : Pattern) (selected : d14046 q = 0) : d122373 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d14046, d122373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14046, d122373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14047 q = 0) : d122374 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d14047, d122374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14047, d122374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14048 q = 0) : d122375 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d14048, d122375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14048, d122375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14049 q = 0) : d122376 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d14049, d122376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14049, d122376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14202 q = 0) : d122497 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d14202, d122497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14202, d122497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9386 q selected
  have h11 (q : Pattern) (selected : d14203 q = 0) : d122498 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d14203, d122498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14203, d122498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14204 q = 0) : d122499 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d14204, d122499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14204, d122499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d14205 q = 0) : d122500 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d14205, d122500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14205, d122500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14206 q = 0) : d122501 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d14206, d122501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14206, d122501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14207 q = 0) : d122502 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d14207, d122502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14207, d122502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9388 (p : Pattern) (selected : d14210 p = 0) : d122505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14080 q = 0) : d122407 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, d122407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9362 q selected
    | true =>
      simp only [d14080, d122407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9346 q selected
  have h2 (q : Pattern) (selected : d14081 q = 0) : d122408 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, d122408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14081, d122408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14082 q = 0) : d122409 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d122409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14082, d122409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d13982 q = 0) : d122309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9346 q selected
    | true =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h5 (q : Pattern) (selected : d13983 q = 0) : d122310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13984 q = 0) : d122311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14083 q = 0) : d122410 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, d122410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14083, d122410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14208 q = 0) : d122503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14208, d122503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14208, d122503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14209 q = 0) : d122504 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14209, d122504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14209, d122504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14210 q = 0) : d122505 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14210, d122505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14210, d122505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9389 (p : Pattern) (selected : d14214 p = 0) : d122509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13982 q = 0) : d122309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9346 q selected
    | true =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h2 (q : Pattern) (selected : d13983 q = 0) : d122310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d13984 q = 0) : d122311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14208 q = 0) : d122503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14208, d122503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14208, d122503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14213 q = 0) : d122508 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14213, d122508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14213, d122508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14214 q = 0) : d122509 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14214, d122509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14214, d122509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9390 (p : Pattern) (selected : d14220 p = 0) : d122515 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14211 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9388 q selected
    | true =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14212 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14217 q = 0) : d122512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14218 q = 0) : d122513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14218, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14219 q = 0) : d122514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14219, d122514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14219, d122514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14220 q = 0) : d122515 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14220, d122515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14220, d122515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9391 (p : Pattern) (selected : d14224 p = 0) : d122519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14221 q = 0) : d122516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14222 q = 0) : d122517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14222, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14223 q = 0) : d122518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14223, d122518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14223, d122518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14224 q = 0) : d122519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14224, d122519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14224, d122519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9392 (p : Pattern) (selected : d14230 p = 0) : d122525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14225 q = 0) : d122520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d122520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9390 q selected
    | true =>
      simp only [d14225, d122520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9391 q selected
  have h2 (q : Pattern) (selected : d14226 q = 0) : d122521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d122521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14226, d122521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14227 q = 0) : d122522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d122522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14227, d122522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14228 q = 0) : d122523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d122523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14228, d122523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14229 q = 0) : d122524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d122524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14229, d122524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14230 q = 0) : d122525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14230, d122525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14230, d122525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9393 (p : Pattern) (selected : d14233 p = 0) : d122528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14211 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9388 q selected
    | true =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14212 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14217 q = 0) : d122512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14218 q = 0) : d122513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14218, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14219 q = 0) : d122514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14219, d122514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14219, d122514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14233 q = 0) : d122528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14233, d122528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14233, d122528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9394 (p : Pattern) (selected : d14234 p = 0) : d122529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14221 q = 0) : d122516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14222 q = 0) : d122517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14222, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14223 q = 0) : d122518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14223, d122518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14223, d122518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14234 q = 0) : d122529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14234, d122529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14234, d122529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9395 (p : Pattern) (selected : d14240 p = 0) : d122535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14225 q = 0) : d122520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d122520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9390 q selected
    | true =>
      simp only [d14225, d122520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9391 q selected
  have h2 (q : Pattern) (selected : d14226 q = 0) : d122521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d122521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14226, d122521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14227 q = 0) : d122522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d122522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14227, d122522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14228 q = 0) : d122523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d122523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14228, d122523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14229 q = 0) : d122524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d122524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14229, d122524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14235 q = 0) : d122530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, d122530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9393 q selected
    | true =>
      simp only [d14235, d122530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9394 q selected
  have h7 (q : Pattern) (selected : d14236 q = 0) : d122531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d122531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14236, d122531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14237 q = 0) : d122532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d122532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14237, d122532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14238 q = 0) : d122533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d122533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14238, d122533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14239 q = 0) : d122534 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d122534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14239, d122534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14240 q = 0) : d122535 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14240, d122535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14240, d122535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9396 (p : Pattern) (selected : d14245 p = 0) : d122540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14211 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9388 q selected
    | true =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14212 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14217 q = 0) : d122512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14218 q = 0) : d122513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14218, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14244 q = 0) : d122539 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14244, d122539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14244, d122539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14245 q = 0) : d122540 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14245, d122540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14245, d122540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9397 (p : Pattern) (selected : d14247 p = 0) : d122542 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14221 q = 0) : d122516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14222 q = 0) : d122517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14222, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14246 q = 0) : d122541 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14246, d122541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14246, d122541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14247 q = 0) : d122542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14247, d122542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14247, d122542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9398 (p : Pattern) (selected : d14254 p = 0) : d122549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14211 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9388 q selected
    | true =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14212 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14217 q = 0) : d122512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14252 q = 0) : d122547 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14252, d122547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14252, d122547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14253 q = 0) : d122548 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14253, d122548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14253, d122548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14254 q = 0) : d122549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14254, d122549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14254, d122549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9399 (p : Pattern) (selected : d14257 p = 0) : d122552 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14221 q = 0) : d122516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14255 q = 0) : d122550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14255, d122550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14255, d122550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14256 q = 0) : d122551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14256, d122551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14256, d122551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14257 q = 0) : d122552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14257, d122552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14257, d122552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9400 (p : Pattern) (selected : d14263 p = 0) : d122558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d543 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d544 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d545 q = 0) : d52292 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d546 q = 0) : d52293 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14261 q = 0) : d122556 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14261, d122556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14261, d122556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12748 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d12749 q = 0) : d113135 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14262 q = 0) : d122557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14262, d122557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14262, d122557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d14263 q = 0) : d122558 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14263, d122558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14263, d122558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9401 (p : Pattern) (selected : d14267 p = 0) : d122562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12493 q = 0) : d112927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12494 q = 0) : d112928 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14078 q = 0) : d122405 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14078, d122405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14078, d122405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d27 q = 0) : d51879 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d28 q = 0) : d51880 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d29 q = 0) : d51881 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d14267 q = 0) : d122562 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14267, d122562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14267, d122562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9402 (p : Pattern) (selected : d14273 p = 0) : d122568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14264 q = 0) : d122559 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14264, d122559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9400 q selected
    | true =>
      simp only [d14264, d122559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9362 q selected
  have h2 (q : Pattern) (selected : d14265 q = 0) : d122560 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14265, d122560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14265, d122560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14266 q = 0) : d122561 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14266, d122561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14266, d122561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14268 q = 0) : d122563 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14268, d122563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9362 q selected
    | true =>
      simp only [d14268, d122563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9401 q selected
  have h5 (q : Pattern) (selected : d14269 q = 0) : d122564 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14269, d122564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14269, d122564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14270 q = 0) : d122565 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14270, d122565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14270, d122565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14271 q = 0) : d122566 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14271, d122566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14271, d122566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14080 q = 0) : d122407 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, d122407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9362 q selected
    | true =>
      simp only [d14080, d122407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9346 q selected
  have h9 (q : Pattern) (selected : d14081 q = 0) : d122408 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, d122408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14081, d122408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14082 q = 0) : d122409 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d122409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14082, d122409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d13982 q = 0) : d122309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9346 q selected
    | true =>
      simp only [d13982, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
  have h12 (q : Pattern) (selected : d13983 q = 0) : d122310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13983, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d13984 q = 0) : d122311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13984, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14083 q = 0) : d122410 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, d122410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14083, d122410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14272 q = 0) : d122567 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14272, d122567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14272, d122567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14273 q = 0) : d122568 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14273, d122568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d14273, d122568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro9403 (p : Pattern) (selected : d14279 p = 0) : d122574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14274 q = 0) : d122569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14274, d122569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9402 q selected
    | true =>
      simp only [d14274, d122569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14275 q = 0) : d122570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14275, d122570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14275, d122570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14211 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9388 q selected
    | true =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14212 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14276 q = 0) : d122571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14276, d122571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14276, d122571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14277 q = 0) : d122572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14277, d122572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14277, d122572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14278 q = 0) : d122573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14278, d122573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14278, d122573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14279 q = 0) : d122574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14279, d122574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14279, d122574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9404 (p : Pattern) (selected : d14285 p = 0) : d122406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d574 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d576 q = 0) : d52120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d576, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d576, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d577 q = 0) : d52121 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d577, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d577, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14281 q = 0) : d122404 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14281, d122404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14281, d122404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9512 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
    | true =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9514 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9514, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14282 q = 0) : d112927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14282, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14282, d112927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14283 q = 0) : d112928 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14283, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14283, d112928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14284 q = 0) : d122405 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14284, d122405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14284, d122405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d14285 q = 0) : d122406 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14285, d122406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14285, d122406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9405 (p : Pattern) (selected : d14292 p = 0) : d122505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14286 q = 0) : d122407 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14286, d122407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9404 q selected
    | true =>
      simp only [d14286, d122407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9365 q selected
  have h2 (q : Pattern) (selected : d14287 q = 0) : d122408 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14287, d122408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14287, d122408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14288 q = 0) : d122409 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14288, d122409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14288, d122409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14095 q = 0) : d122309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14095, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9365 q selected
    | true =>
      simp only [d14095, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
  have h5 (q : Pattern) (selected : d14096 q = 0) : d122310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14096, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14096, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14097 q = 0) : d122311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14097, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14097, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14289 q = 0) : d122410 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14289, d122410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14289, d122410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14290 q = 0) : d122503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14290, d122503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14290, d122503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14291 q = 0) : d122504 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14291, d122504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14291, d122504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14292 q = 0) : d122505 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14292, d122505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14292, d122505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9406 (p : Pattern) (selected : d14296 p = 0) : d122509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14095 q = 0) : d122309 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14095, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9365 q selected
    | true =>
      simp only [d14095, d122309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
  have h2 (q : Pattern) (selected : d14096 q = 0) : d122310 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14096, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14096, d122310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14097 q = 0) : d122311 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14097, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14097, d122311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14290 q = 0) : d122503 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14290, d122503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14290, d122503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14295 q = 0) : d122508 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14295, d122508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14295, d122508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14296 q = 0) : d122509 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14296, d122509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14296, d122509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9407 (p : Pattern) (selected : d14302 p = 0) : d122515 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14293 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14293, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9405 q selected
    | true =>
      simp only [d14293, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14294 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14294, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14294, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14297 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14297, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9406 q selected
    | true =>
      simp only [d14297, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14298 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14298, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14298, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14299 q = 0) : d122512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14299, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14299, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14300 q = 0) : d122513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14300, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14300, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14301 q = 0) : d122514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14301, d122514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14301, d122514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14302 q = 0) : d122515 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14302, d122515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14302, d122515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9408 (p : Pattern) (selected : d14306 p = 0) : d122519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14297 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14297, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9406 q selected
    | true =>
      simp only [d14297, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14298 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14298, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14298, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14303 q = 0) : d122516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14303, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14303, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14304 q = 0) : d122517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14304, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14304, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14305 q = 0) : d122518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14305, d122518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14305, d122518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14306 q = 0) : d122519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14306, d122519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14306, d122519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9409 (p : Pattern) (selected : d14312 p = 0) : d122580 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14211 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9388 q selected
    | true =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14212 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14309 q = 0) : d122577 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14309, d122577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14309, d122577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14310 q = 0) : d122578 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14310, d122578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14310, d122578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14311 q = 0) : d122579 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14311, d122579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14311, d122579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14312 q = 0) : d122580 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14312, d122580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14312, d122580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9410 (p : Pattern) (selected : d14318 p = 0) : d122586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14248 q = 0) : d122543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14248, d122543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9396 q selected
    | true =>
      simp only [d14248, d122543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9397 q selected
  have h2 (q : Pattern) (selected : d14249 q = 0) : d122544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14249, d122544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14249, d122544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14250 q = 0) : d122545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14250, d122545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14250, d122545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14251 q = 0) : d122546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14251, d122546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14251, d122546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14258 q = 0) : d122553 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14258, d122553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9398 q selected
    | true =>
      simp only [d14258, d122553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9399 q selected
  have h6 (q : Pattern) (selected : d14259 q = 0) : d122554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14259, d122554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14259, d122554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14260 q = 0) : d122555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14260, d122555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14260, d122555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14280 q = 0) : d122575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14280, d122575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9403 q selected
    | true =>
      simp only [d14280, d122575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9390 q selected
  have h9 (q : Pattern) (selected : d14307 q = 0) : d122520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14307, d122520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9407 q selected
    | true =>
      simp only [d14307, d122520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9408 q selected
  have h10 (q : Pattern) (selected : d14308 q = 0) : d122576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14308, d122576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14308, d122576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14313 q = 0) : d122581 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14313, d122581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9409 q selected
    | true =>
      simp only [d14313, d122581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d14314 q = 0) : d122582 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14314, d122582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d14314, d122582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14315 q = 0) : d122583 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14315, d122583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14315, d122583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14316 q = 0) : d122584 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14316, d122584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14316, d122584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14317 q = 0) : d122585 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14317, d122585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14317, d122585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14318 q = 0) : d122586 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14318, d122586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14318, d122586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro9411 (p : Pattern) (selected : d14319 p = 0) : d122587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14211 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9388 q selected
    | true =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14212 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14217 q = 0) : d122512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14218 q = 0) : d122513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14218, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14244 q = 0) : d122539 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14244, d122539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14244, d122539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14319 q = 0) : d122587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14319, d122587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14319, d122587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9412 (p : Pattern) (selected : d14320 p = 0) : d122588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14221 q = 0) : d122516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14222 q = 0) : d122517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14222, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14246 q = 0) : d122541 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14246, d122541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14246, d122541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14320 q = 0) : d122588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14320, d122588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14320, d122588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9413 (p : Pattern) (selected : d14325 p = 0) : d122593 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14211 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9388 q selected
    | true =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14212 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14217 q = 0) : d122512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14217, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14252 q = 0) : d122547 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14252, d122547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14252, d122547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14253 q = 0) : d122548 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14253, d122548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14253, d122548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14325 q = 0) : d122593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14325, d122593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14325, d122593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9414 (p : Pattern) (selected : d14326 p = 0) : d122594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14215 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9389 q selected
    | true =>
      simp only [d14215, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14216 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14216, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14221 q = 0) : d122516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14221, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14255 q = 0) : d122550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14255, d122550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14255, d122550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14256 q = 0) : d122551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14256, d122551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14256, d122551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14326 q = 0) : d122594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14326, d122594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14326, d122594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9415 (p : Pattern) (selected : d14330 p = 0) : d122598 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14274 q = 0) : d122569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14274, d122569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9402 q selected
    | true =>
      simp only [d14274, d122569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14275 q = 0) : d122570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14275, d122570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14275, d122570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14211 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9388 q selected
    | true =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14212 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14276 q = 0) : d122571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14276, d122571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14276, d122571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14277 q = 0) : d122572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14277, d122572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14277, d122572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14278 q = 0) : d122573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14278, d122573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14278, d122573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14330 q = 0) : d122598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14330, d122598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14330, d122598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9416 (p : Pattern) (selected : d14332 p = 0) : d122528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14293 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14293, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9405 q selected
    | true =>
      simp only [d14293, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14294 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14294, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14294, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14297 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14297, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9406 q selected
    | true =>
      simp only [d14297, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14298 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14298, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14298, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14299 q = 0) : d122512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14299, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14299, d122512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14300 q = 0) : d122513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14300, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14300, d122513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14301 q = 0) : d122514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14301, d122514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14301, d122514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14332 q = 0) : d122528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14332, d122528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14332, d122528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9417 (p : Pattern) (selected : d14333 p = 0) : d122529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14297 q = 0) : d122510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14297, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9406 q selected
    | true =>
      simp only [d14297, d122510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14298 q = 0) : d122511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14298, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14298, d122511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14303 q = 0) : d122516 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14303, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14303, d122516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14304 q = 0) : d122517 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14304, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14304, d122517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14305 q = 0) : d122518 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14305, d122518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14305, d122518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14333 q = 0) : d122529 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14333, d122529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14333, d122529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9418 (p : Pattern) (selected : d14336 p = 0) : d122601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14211 q = 0) : d122506 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9388 q selected
    | true =>
      simp only [d14211, d122506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14212 q = 0) : d122507 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14212, d122507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14309 q = 0) : d122577 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14309, d122577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14309, d122577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14310 q = 0) : d122578 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14310, d122578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14310, d122578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14311 q = 0) : d122579 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14311, d122579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14311, d122579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14336 q = 0) : d122601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14336, d122601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14336, d122601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9419 (p : Pattern) (selected : d14342 p = 0) : d122607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14248 q = 0) : d122543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14248, d122543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9396 q selected
    | true =>
      simp only [d14248, d122543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9397 q selected
  have h2 (q : Pattern) (selected : d14249 q = 0) : d122544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14249, d122544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14249, d122544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14250 q = 0) : d122545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14250, d122545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14250, d122545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14251 q = 0) : d122546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14251, d122546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14251, d122546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14258 q = 0) : d122553 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14258, d122553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9398 q selected
    | true =>
      simp only [d14258, d122553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9399 q selected
  have h6 (q : Pattern) (selected : d14259 q = 0) : d122554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14259, d122554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14259, d122554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14260 q = 0) : d122555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14260, d122555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14260, d122555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14280 q = 0) : d122575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14280, d122575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9403 q selected
    | true =>
      simp only [d14280, d122575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9390 q selected
  have h9 (q : Pattern) (selected : d14307 q = 0) : d122520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14307, d122520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9407 q selected
    | true =>
      simp only [d14307, d122520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9408 q selected
  have h10 (q : Pattern) (selected : d14308 q = 0) : d122576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14308, d122576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14308, d122576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14313 q = 0) : d122581 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14313, d122581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9409 q selected
    | true =>
      simp only [d14313, d122581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d14314 q = 0) : d122582 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14314, d122582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d14314, d122582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14315 q = 0) : d122583 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14315, d122583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14315, d122583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14316 q = 0) : d122584 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14316, d122584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14316, d122584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14317 q = 0) : d122585 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14317, d122585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14317, d122585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14321 q = 0) : d122589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14321, d122589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9411 q selected
    | true =>
      simp only [d14321, d122589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9412 q selected
  have h17 (q : Pattern) (selected : d14322 q = 0) : d122590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14322, d122590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14322, d122590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d14323 q = 0) : d122591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14323, d122591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d14323, d122591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d14324 q = 0) : d122592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14324, d122592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14324, d122592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d14327 q = 0) : d122595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14327, d122595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9413 q selected
    | true =>
      simp only [d14327, d122595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9414 q selected
  have h21 (q : Pattern) (selected : d14328 q = 0) : d122596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14328, d122596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14328, d122596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d14329 q = 0) : d122597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14329, d122597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d14329, d122597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d14331 q = 0) : d122599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14331, d122599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9415 q selected
    | true =>
      simp only [d14331, d122599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9393 q selected
  have h24 (q : Pattern) (selected : d14334 q = 0) : d122530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14334, d122530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9416 q selected
    | true =>
      simp only [d14334, d122530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9417 q selected
  have h25 (q : Pattern) (selected : d14335 q = 0) : d122600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14335, d122600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d14335, d122600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d14337 q = 0) : d122602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14337, d122602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9418 q selected
    | true =>
      simp only [d14337, d122602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d14338 q = 0) : d122603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14338, d122603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d14338, d122603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d14339 q = 0) : d122604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14339, d122604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d14339, d122604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d14340 q = 0) : d122605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14340, d122605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d14340, d122605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d14341 q = 0) : d122606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14341, d122606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d14341, d122606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d14342 q = 0) : d122607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14342, d122607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d14342, d122607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro9420 (p : Pattern) (selected : d14349 p = 0) : d122614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14225 q = 0) : d122520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d122520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9390 q selected
    | true =>
      simp only [d14225, d122520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9391 q selected
  have h2 (q : Pattern) (selected : d14226 q = 0) : d122521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d122521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14226, d122521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14227 q = 0) : d122522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d122522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14227, d122522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14228 q = 0) : d122523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d122523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14228, d122523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14229 q = 0) : d122524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d122524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14229, d122524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14344 q = 0) : d122609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14344, d122609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9391 q selected
    | true =>
      simp only [d14344, d122609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14345 q = 0) : d122610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14345, d122610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14345, d122610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14346 q = 0) : d122611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14346, d122611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14346, d122611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14347 q = 0) : d122612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14347, d122612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14347, d122612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14348 q = 0) : d122613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14348, d122613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14348, d122613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14349 q = 0) : d122614 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14349, d122614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14349, d122614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9421 (p : Pattern) (selected : d14355 p = 0) : d122620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14344 q = 0) : d122609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14344, d122609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9391 q selected
    | true =>
      simp only [d14344, d122609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14345 q = 0) : d122610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14345, d122610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14345, d122610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14346 q = 0) : d122611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14346, d122611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14346, d122611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14347 q = 0) : d122612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14347, d122612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14347, d122612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14348 q = 0) : d122613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14348, d122613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14348, d122613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14350 q = 0) : d122615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14350, d122615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9394 q selected
    | true =>
      simp only [d14350, d122615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14351 q = 0) : d122616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14351, d122616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14351, d122616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14352 q = 0) : d122617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14352, d122617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14352, d122617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14353 q = 0) : d122618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14353, d122618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14353, d122618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14354 q = 0) : d122619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14354, d122619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14354, d122619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14355 q = 0) : d122620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14355, d122620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14355, d122620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9422 (p : Pattern) (selected : d14362 p = 0) : d122627 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14331 q = 0) : d122599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14331, d122599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9415 q selected
    | true =>
      simp only [d14331, d122599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9393 q selected
  have h2 (q : Pattern) (selected : d14334 q = 0) : d122530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14334, d122530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9416 q selected
    | true =>
      simp only [d14334, d122530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9417 q selected
  have h3 (q : Pattern) (selected : d14335 q = 0) : d122600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14335, d122600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14335, d122600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14337 q = 0) : d122602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14337, d122602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9418 q selected
    | true =>
      simp only [d14337, d122602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14338 q = 0) : d122603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14338, d122603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14338, d122603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14339 q = 0) : d122604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14339, d122604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14339, d122604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14360 q = 0) : d122625 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14360, d122625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14360, d122625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14361 q = 0) : d122626 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14361, d122626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14361, d122626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14362 q = 0) : d122627 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14362, d122627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14362, d122627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9423 (p : Pattern) (selected : d14364 p = 0) : d122629 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14350 q = 0) : d122615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14350, d122615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9394 q selected
    | true =>
      simp only [d14350, d122615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14351 q = 0) : d122616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14351, d122616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14351, d122616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14352 q = 0) : d122617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14352, d122617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14352, d122617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14353 q = 0) : d122618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14353, d122618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14353, d122618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14354 q = 0) : d122619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14354, d122619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14354, d122619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14364 q = 0) : d122629 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14364, d122629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14364, d122629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9424 (p : Pattern) (selected : d14372 p = 0) : d122637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d659 q = 0) : d52363 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
  have h2 (q : Pattern) (selected : d543 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro277 q selected
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d660 q = 0) : d52364 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d544 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d661 q = 0) : d52365 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d662 q = 0) : d52366 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14370 q = 0) : d122635 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14370, d122635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14370, d122635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12858 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h9 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d12859 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d12860 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d12861 q = 0) : d113217 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14371 q = 0) : d122636 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14371, d122636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d14371, d122636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14372 q = 0) : d122637 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14372, d122637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14372, d122637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9425 (p : Pattern) (selected : d14376 p = 0) : d122641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12599 q = 0) : d113007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
  have h2 (q : Pattern) (selected : d9382 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6607 q selected
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12600 q = 0) : d113008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9384 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12601 q = 0) : d113009 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12602 q = 0) : d113010 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14155 q = 0) : d122465 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14155, d122465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14155, d122465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d66 q = 0) : d51918 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
  have h9 (q : Pattern) (selected : d25 q = 0) : d51877 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro187 q selected
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d67 q = 0) : d51919 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d26 q = 0) : d51878 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d68 q = 0) : d51920 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d69 q = 0) : d51921 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d70 q = 0) : d51922 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14376 q = 0) : d122641 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14376, d122641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14376, d122641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9426 (p : Pattern) (selected : d14382 p = 0) : d122647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14373 q = 0) : d122638 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14373, d122638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9424 q selected
    | true =>
      simp only [d14373, d122638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9378 q selected
  have h2 (q : Pattern) (selected : d14374 q = 0) : d122639 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14374, d122639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14374, d122639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14375 q = 0) : d122640 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14375, d122640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14375, d122640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14377 q = 0) : d122642 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14377, d122642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9378 q selected
    | true =>
      simp only [d14377, d122642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9425 q selected
  have h5 (q : Pattern) (selected : d14378 q = 0) : d122643 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14378, d122643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14378, d122643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14379 q = 0) : d122644 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14379, d122644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14379, d122644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14380 q = 0) : d122645 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14380, d122645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14380, d122645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14157 q = 0) : d122467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, d122467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9378 q selected
    | true =>
      simp only [d14157, d122467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9353 q selected
  have h9 (q : Pattern) (selected : d14158 q = 0) : d122468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, d122468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14158, d122468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14159 q = 0) : d122469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d122469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14159, d122469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14021 q = 0) : d122348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9353 q selected
    | true =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h12 (q : Pattern) (selected : d14022 q = 0) : d122349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d14023 q = 0) : d122350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14160 q = 0) : d122470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, d122470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14160, d122470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14381 q = 0) : d122646 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14381, d122646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14381, d122646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14382 q = 0) : d122647 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14382, d122647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d14382, d122647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro9427 (p : Pattern) (selected : d14387 p = 0) : d122652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14157 q = 0) : d122467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, d122467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9378 q selected
    | true =>
      simp only [d14157, d122467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9353 q selected
  have h2 (q : Pattern) (selected : d14158 q = 0) : d122468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, d122468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14158, d122468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14159 q = 0) : d122469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d122469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14159, d122469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14021 q = 0) : d122348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9353 q selected
    | true =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h5 (q : Pattern) (selected : d14022 q = 0) : d122349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14023 q = 0) : d122350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14160 q = 0) : d122470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, d122470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14160, d122470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14385 q = 0) : d122650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14385, d122650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14385, d122650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14386 q = 0) : d122651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14386, d122651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14386, d122651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14387 q = 0) : d122652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14387, d122652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14387, d122652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9428 (p : Pattern) (selected : d14393 p = 0) : d122658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14383 q = 0) : d122648 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14383, d122648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9426 q selected
    | true =>
      simp only [d14383, d122648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14384 q = 0) : d122649 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14384, d122649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14384, d122649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14388 q = 0) : d122653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, d122653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9427 q selected
    | true =>
      simp only [d14388, d122653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14389 q = 0) : d122654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, d122654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14389, d122654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14390 q = 0) : d122655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14390, d122655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14390, d122655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14391 q = 0) : d122656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14391, d122656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14391, d122656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14392 q = 0) : d122657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14392, d122657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14392, d122657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14393 q = 0) : d122658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14393, d122658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14393, d122658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9429 (p : Pattern) (selected : d14395 p = 0) : d122660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14021 q = 0) : d122348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9353 q selected
    | true =>
      simp only [d14021, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h2 (q : Pattern) (selected : d14022 q = 0) : d122349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14022, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14023 q = 0) : d122350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14023, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14385 q = 0) : d122650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14385, d122650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14385, d122650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14394 q = 0) : d122659 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14394, d122659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14394, d122659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14395 q = 0) : d122660 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14395, d122660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14395, d122660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9430 (p : Pattern) (selected : d14401 p = 0) : d122666 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14388 q = 0) : d122653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, d122653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9427 q selected
    | true =>
      simp only [d14388, d122653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14389 q = 0) : d122654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, d122654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14389, d122654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14396 q = 0) : d122661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14396, d122661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9429 q selected
    | true =>
      simp only [d14396, d122661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14397 q = 0) : d122662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14397, d122662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14397, d122662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14398 q = 0) : d122663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14398, d122663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14398, d122663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14399 q = 0) : d122664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14399, d122664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14399, d122664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14400 q = 0) : d122665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14400, d122665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14400, d122665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14401 q = 0) : d122666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14401, d122666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14401, d122666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9431 (p : Pattern) (selected : d14409 p = 0) : d122466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d691 q = 0) : d52178 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d691, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d691, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
  have h2 (q : Pattern) (selected : d574 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d692 q = 0) : d52179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d692, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d692, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d575 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d693 q = 0) : d52180 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d693, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d693, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d694 q = 0) : d52181 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d694, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d694, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14403 q = 0) : d122464 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14403, d122464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14403, d122464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14404 q = 0) : d113007 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14404, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14404, d113007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
  have h9 (q : Pattern) (selected : d9512 q = 0) : d101015 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6628 q selected
    | true =>
      simp only [d9512, d101015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14405 q = 0) : d113008 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14405, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14405, d113008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9514 q = 0) : d101017 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9514, d101017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d14406 q = 0) : d113009 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14406, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14406, d113009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d14407 q = 0) : d113010 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14407, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14407, d113010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14408 q = 0) : d122465 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14408, d122465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d14408, d122465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14409 q = 0) : d122466 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14409, d122466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14409, d122466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9432 (p : Pattern) (selected : d14416 p = 0) : d122652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14410 q = 0) : d122467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14410, d122467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9431 q selected
    | true =>
      simp only [d14410, d122467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9381 q selected
  have h2 (q : Pattern) (selected : d14411 q = 0) : d122468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14411, d122468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14411, d122468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14412 q = 0) : d122469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14412, d122469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14412, d122469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14172 q = 0) : d122348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14172, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9381 q selected
    | true =>
      simp only [d14172, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h5 (q : Pattern) (selected : d14173 q = 0) : d122349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14173, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14173, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14174 q = 0) : d122350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14174, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14174, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14413 q = 0) : d122470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14413, d122470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14413, d122470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14414 q = 0) : d122650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14414, d122650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14414, d122650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14415 q = 0) : d122651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14415, d122651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14415, d122651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14416 q = 0) : d122652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14416, d122652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14416, d122652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9433 (p : Pattern) (selected : d14420 p = 0) : d122660 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14172 q = 0) : d122348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14172, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9381 q selected
    | true =>
      simp only [d14172, d122348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h2 (q : Pattern) (selected : d14173 q = 0) : d122349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14173, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14173, d122349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14174 q = 0) : d122350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14174, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14174, d122350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14414 q = 0) : d122650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14414, d122650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14414, d122650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14419 q = 0) : d122659 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14419, d122659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14419, d122659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14420 q = 0) : d122660 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14420, d122660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14420, d122660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9434 (p : Pattern) (selected : d14426 p = 0) : d122666 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14417 q = 0) : d122653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14417, d122653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9432 q selected
    | true =>
      simp only [d14417, d122653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14418 q = 0) : d122654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14418, d122654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14418, d122654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14421 q = 0) : d122661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14421, d122661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9433 q selected
    | true =>
      simp only [d14421, d122661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14422 q = 0) : d122662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14422, d122662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14422, d122662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14423 q = 0) : d122663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14423, d122663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14423, d122663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14424 q = 0) : d122664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14424, d122664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14424, d122664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14425 q = 0) : d122665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14425, d122665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14425, d122665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14426 q = 0) : d122666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14426, d122666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14426, d122666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9435 (p : Pattern) (selected : d14430 p = 0) : d122671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14421 q = 0) : d122661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14421, d122661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9433 q selected
    | true =>
      simp only [d14421, d122661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14422 q = 0) : d122662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14422, d122662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14422, d122662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14427 q = 0) : d122668 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14427, d122668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14427, d122668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14428 q = 0) : d122669 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14428, d122669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14428, d122669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14429 q = 0) : d122670 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14429, d122670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14429, d122670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14430 q = 0) : d122671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14430, d122671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14430, d122671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9436 (p : Pattern) (selected : d14436 p = 0) : d122677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14388 q = 0) : d122653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, d122653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9427 q selected
    | true =>
      simp only [d14388, d122653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14389 q = 0) : d122654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, d122654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14389, d122654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14433 q = 0) : d122674 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14433, d122674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14433, d122674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14434 q = 0) : d122675 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14434, d122675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14434, d122675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14435 q = 0) : d122676 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14435, d122676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14435, d122676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14436 q = 0) : d122677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14436, d122677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14436, d122677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9437 (p : Pattern) (selected : d14442 p = 0) : d122683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14402 q = 0) : d122667 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14402, d122667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9428 q selected
    | true =>
      simp only [d14402, d122667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9430 q selected
  have h2 (q : Pattern) (selected : d14431 q = 0) : d122672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14431, d122672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9434 q selected
    | true =>
      simp only [d14431, d122672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9435 q selected
  have h3 (q : Pattern) (selected : d14432 q = 0) : d122673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14432, d122673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14432, d122673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14437 q = 0) : d122678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14437, d122678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9436 q selected
    | true =>
      simp only [d14437, d122678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14438 q = 0) : d122679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14438, d122679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14438, d122679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14439 q = 0) : d122680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14439, d122680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14439, d122680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14440 q = 0) : d122681 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14440, d122681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14440, d122681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14441 q = 0) : d122682 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14441, d122682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14441, d122682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14442 q = 0) : d122683 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14442, d122683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14442, d122683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9438 (p : Pattern) (selected : d14447 p = 0) : d122671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14396 q = 0) : d122661 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14396, d122661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9429 q selected
    | true =>
      simp only [d14396, d122661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14397 q = 0) : d122662 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14397, d122662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14397, d122662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14444 q = 0) : d122668 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14444, d122668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14444, d122668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14445 q = 0) : d122669 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14445, d122669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14445, d122669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14446 q = 0) : d122670 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14446, d122670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14446, d122670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14447 q = 0) : d122671 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14447, d122671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14447, d122671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9439 (p : Pattern) (selected : d14453 p = 0) : d122690 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14448 q = 0) : d122685 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14448, d122685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9438 q selected
    | true =>
      simp only [d14448, d122685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14449 q = 0) : d122686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14449, d122686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14449, d122686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14450 q = 0) : d122687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14450, d122687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14450, d122687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14451 q = 0) : d122688 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14451, d122688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14451, d122688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14452 q = 0) : d122689 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14452, d122689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14452, d122689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14453 q = 0) : d122690 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14453, d122690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14453, d122690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9440 (p : Pattern) (selected : d14459 p = 0) : d122696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14231 q = 0) : d122526 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14231, d122526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14231, d122526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9392 q selected
  have h2 (q : Pattern) (selected : d14232 q = 0) : d122527 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14232, d122527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14232, d122527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14241 q = 0) : d122536 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, d122536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9392 q selected
    | true =>
      simp only [d14241, d122536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9395 q selected
  have h4 (q : Pattern) (selected : d14242 q = 0) : d122537 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, d122537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14242, d122537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14243 q = 0) : d122538 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14243, d122538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14243, d122538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14343 q = 0) : d122608 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14343, d122608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9410 q selected
    | true =>
      simp only [d14343, d122608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9419 q selected
  have h7 (q : Pattern) (selected : d14356 q = 0) : d122621 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14356, d122621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9420 q selected
    | true =>
      simp only [d14356, d122621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9421 q selected
  have h8 (q : Pattern) (selected : d14357 q = 0) : d122622 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14357, d122622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14357, d122622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14358 q = 0) : d122623 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14358, d122623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14358, d122623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14359 q = 0) : d122624 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14359, d122624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14359, d122624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14363 q = 0) : d122628 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14363, d122628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14363, d122628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9422 q selected
  have h12 (q : Pattern) (selected : d14365 q = 0) : d122630 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14365, d122630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14365, d122630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9423 q selected
  have h13 (q : Pattern) (selected : d14366 q = 0) : d122631 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14366, d122631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d14366, d122631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14367 q = 0) : d122632 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14367, d122632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d14367, d122632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14368 q = 0) : d122633 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14368, d122633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d14368, d122633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d14369 q = 0) : d122634 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d14369, d122634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14369, d122634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d14443 q = 0) : d122684 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14443, d122684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14443, d122684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9437 q selected
  have h18 (q : Pattern) (selected : d14454 q = 0) : d122691 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14454, d122691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14454, d122691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9439 q selected
  have h19 (q : Pattern) (selected : d14455 q = 0) : d122692 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14455, d122692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d14455, d122692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d14456 q = 0) : d122693 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14456, d122693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d14456, d122693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d14457 q = 0) : d122694 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14457, d122694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d14457, d122694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d14458 q = 0) : d122695 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d14458, d122695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d14458, d122695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d14459 q = 0) : d122696 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d14459, d122696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d14459, d122696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro9441 (p : Pattern) (selected : d14465 p = 0) : d122702 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14460 q = 0) : d122697 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d14460, d122697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14460, d122697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9440 q selected
  have h2 (q : Pattern) (selected : d14461 q = 0) : d122698 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d14461, d122698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14461, d122698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14462 q = 0) : d122699 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d14462, d122699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14462, d122699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14463 q = 0) : d122700 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d14463, d122700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14463, d122700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14464 q = 0) : d122701 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d14464, d122701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14464, d122701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14465 q = 0) : d122702 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d14465, d122702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14465, d122702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9442 (p : Pattern) (selected : d14467 p = 0) : d122704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d319 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d320 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d321 q = 0) : d52120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d322 q = 0) : d52121 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14077 q = 0) : d122404 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14077, d122404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14077, d122404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d753 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d754 q = 0) : d52431 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d757 q = 0) : d52434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d14467 q = 0) : d122704 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14467, d122704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14467, d122704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9443 (p : Pattern) (selected : d14477 p = 0) : d122714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14468 q = 0) : d122705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14468, d122705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9400 q selected
    | true =>
      simp only [d14468, d122705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9442 q selected
  have h2 (q : Pattern) (selected : d14469 q = 0) : d122706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14469, d122706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14469, d122706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14470 q = 0) : d122707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, d122707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14470, d122707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14471 q = 0) : d122708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, d122708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9442 q selected
    | true =>
      simp only [d14471, d122708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h5 (q : Pattern) (selected : d14472 q = 0) : d122709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, d122709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14472, d122709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14473 q = 0) : d122710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d122710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14473, d122710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14474 q = 0) : d122711 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, d122711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14474, d122711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14475 q = 0) : d122712 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14475, d122712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14475, d122712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14476 q = 0) : d122713 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14476, d122713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14476, d122713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14477 q = 0) : d122714 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14477, d122714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14477, d122714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9444 (p : Pattern) (selected : d14481 p = 0) : d122718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14471 q = 0) : d122708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, d122708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9442 q selected
    | true =>
      simp only [d14471, d122708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h2 (q : Pattern) (selected : d14472 q = 0) : d122709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, d122709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14472, d122709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14473 q = 0) : d122710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d122710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14473, d122710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14475 q = 0) : d122712 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14475, d122712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14475, d122712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14480 q = 0) : d122717 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14480, d122717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14480, d122717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14481 q = 0) : d122718 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14481, d122718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14481, d122718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9445 (p : Pattern) (selected : d14487 p = 0) : d122724 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14478 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9443 q selected
    | true =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14479 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14484 q = 0) : d122721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14485 q = 0) : d122722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14485, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14486 q = 0) : d122723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, d122723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14486, d122723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14487 q = 0) : d122724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14487, d122724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14487, d122724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9446 (p : Pattern) (selected : d14491 p = 0) : d122728 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14488 q = 0) : d122725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14489 q = 0) : d122726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14489, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14490 q = 0) : d122727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, d122727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14490, d122727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14491 q = 0) : d122728 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14491, d122728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14491, d122728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9447 (p : Pattern) (selected : d14497 p = 0) : d122734 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14492 q = 0) : d122729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d122729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9445 q selected
    | true =>
      simp only [d14492, d122729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9446 q selected
  have h2 (q : Pattern) (selected : d14493 q = 0) : d122730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d122730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14493, d122730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14494 q = 0) : d122731 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d122731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14494, d122731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14495 q = 0) : d122732 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d122732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14495, d122732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14496 q = 0) : d122733 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d122733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14496, d122733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14497 q = 0) : d122734 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14497, d122734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14497, d122734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9448 (p : Pattern) (selected : d14500 p = 0) : d122737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14478 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9443 q selected
    | true =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14479 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14484 q = 0) : d122721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14485 q = 0) : d122722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14485, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14486 q = 0) : d122723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, d122723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14486, d122723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14500 q = 0) : d122737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14500, d122737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14500, d122737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9449 (p : Pattern) (selected : d14501 p = 0) : d122738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14488 q = 0) : d122725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14489 q = 0) : d122726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14489, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14490 q = 0) : d122727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, d122727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14490, d122727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14501 q = 0) : d122738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14501, d122738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14501, d122738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9450 (p : Pattern) (selected : d14507 p = 0) : d122744 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14492 q = 0) : d122729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d122729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9445 q selected
    | true =>
      simp only [d14492, d122729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9446 q selected
  have h2 (q : Pattern) (selected : d14493 q = 0) : d122730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d122730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14493, d122730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14494 q = 0) : d122731 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d122731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14494, d122731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14495 q = 0) : d122732 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d122732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14495, d122732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14496 q = 0) : d122733 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d122733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14496, d122733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14502 q = 0) : d122739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d122739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9448 q selected
    | true =>
      simp only [d14502, d122739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9449 q selected
  have h7 (q : Pattern) (selected : d14503 q = 0) : d122740 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d122740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14503, d122740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14504 q = 0) : d122741 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d122741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14504, d122741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14505 q = 0) : d122742 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d122742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14505, d122742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14506 q = 0) : d122743 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d122743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14506, d122743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14507 q = 0) : d122744 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14507, d122744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14507, d122744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9451 (p : Pattern) (selected : d14512 p = 0) : d122749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14478 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9443 q selected
    | true =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14479 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14484 q = 0) : d122721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14485 q = 0) : d122722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14485, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14511 q = 0) : d122748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, d122748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14511, d122748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14512 q = 0) : d122749 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14512, d122749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14512, d122749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9452 (p : Pattern) (selected : d14514 p = 0) : d122751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14488 q = 0) : d122725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14489 q = 0) : d122726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14489, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14513 q = 0) : d122750 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, d122750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14513, d122750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14514 q = 0) : d122751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14514, d122751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14514, d122751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9453 (p : Pattern) (selected : d14521 p = 0) : d122758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14478 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9443 q selected
    | true =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14479 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14484 q = 0) : d122721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14519 q = 0) : d122756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, d122756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14519, d122756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14520 q = 0) : d122757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, d122757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14520, d122757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14521 q = 0) : d122758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14521, d122758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14521, d122758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9454 (p : Pattern) (selected : d14524 p = 0) : d122761 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14488 q = 0) : d122725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14522 q = 0) : d122759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, d122759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14522, d122759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14523 q = 0) : d122760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, d122760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14523, d122760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14524 q = 0) : d122761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14524, d122761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14524, d122761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9455 (p : Pattern) (selected : d14532 p = 0) : d122769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d834 q = 0) : d52511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d835 q = 0) : d52512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d836 q = 0) : d52513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d837 q = 0) : d52514 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14528 q = 0) : d122765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14528, d122765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14528, d122765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9597 q = 0) : d101177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9599 q = 0) : d101179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14529 q = 0) : d122766 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, d122766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14529, d122766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14530 q = 0) : d122767 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, d122767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14530, d122767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14531 q = 0) : d122768 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14531, d122768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14531, d122768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d14532 q = 0) : d122769 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14532, d122769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14532, d122769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9456 (p : Pattern) (selected : d14536 p = 0) : d122773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12748 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12748, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12749 q = 0) : d113135 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12749, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14262 q = 0) : d122557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14262, d122557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14262, d122557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d753 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d754 q = 0) : d52431 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d757 q = 0) : d52434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d14536 q = 0) : d122773 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14536, d122773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14536, d122773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9457 (p : Pattern) (selected : d14542 p = 0) : d122779 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14533 q = 0) : d122770 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14533, d122770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9455 q selected
    | true =>
      simp only [d14533, d122770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9400 q selected
  have h2 (q : Pattern) (selected : d14534 q = 0) : d122771 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14534, d122771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14534, d122771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14535 q = 0) : d122772 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14535, d122772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14535, d122772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14537 q = 0) : d122774 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14537, d122774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9400 q selected
    | true =>
      simp only [d14537, d122774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9456 q selected
  have h5 (q : Pattern) (selected : d14538 q = 0) : d122775 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14538, d122775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14538, d122775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14539 q = 0) : d122776 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14539, d122776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14539, d122776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14540 q = 0) : d122777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14540, d122777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14540, d122777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14468 q = 0) : d122705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14468, d122705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9400 q selected
    | true =>
      simp only [d14468, d122705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9442 q selected
  have h9 (q : Pattern) (selected : d14469 q = 0) : d122706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14469, d122706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14469, d122706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14470 q = 0) : d122707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, d122707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14470, d122707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14471 q = 0) : d122708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, d122708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9442 q selected
    | true =>
      simp only [d14471, d122708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro320 q selected
  have h12 (q : Pattern) (selected : d14472 q = 0) : d122709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, d122709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14472, d122709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d14473 q = 0) : d122710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d122710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14473, d122710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14474 q = 0) : d122711 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, d122711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14474, d122711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14541 q = 0) : d122778 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14541, d122778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14541, d122778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14542 q = 0) : d122779 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14542, d122779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d14542, d122779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro9458 (p : Pattern) (selected : d14548 p = 0) : d122785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14543 q = 0) : d122780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, d122780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9457 q selected
    | true =>
      simp only [d14543, d122780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14544 q = 0) : d122781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, d122781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14544, d122781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14478 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9443 q selected
    | true =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14479 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14545 q = 0) : d122782 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, d122782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14545, d122782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14546 q = 0) : d122783 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, d122783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14546, d122783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14547 q = 0) : d122784 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, d122784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14547, d122784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14548 q = 0) : d122785 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14548, d122785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14548, d122785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9459 (p : Pattern) (selected : d14554 p = 0) : d122558 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d868 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
    | true =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d869 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d869, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d869, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d870 q = 0) : d52292 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d870, d52292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d870, d52292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d871 q = 0) : d52293 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d871, d52293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d871, d52293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14550 q = 0) : d122556 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14550, d122556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14550, d122556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9671 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
    | true =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9673 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14551 q = 0) : d113134 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14551, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14551, d113134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14552 q = 0) : d113135 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14552, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14552, d113135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14553 q = 0) : d122557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14553, d122557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14553, d122557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d14554 q = 0) : d122558 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14554, d122558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14554, d122558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9460 (p : Pattern) (selected : d14555 p = 0) : d122704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d574 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d576 q = 0) : d52120 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d576, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d576, d52120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d577 q = 0) : d52121 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d577, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d577, d52121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14281 q = 0) : d122404 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14281, d122404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14281, d122404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d876 q = 0) : d52430 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, d52430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d877 q = 0) : d52431 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d877, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d877, d52431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d880 q = 0) : d52434 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d880, d52434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d880, d52434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d14555 q = 0) : d122704 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14555, d122704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14555, d122704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9461 (p : Pattern) (selected : d14565 p = 0) : d122714 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14556 q = 0) : d122705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14556, d122705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9459 q selected
    | true =>
      simp only [d14556, d122705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9460 q selected
  have h2 (q : Pattern) (selected : d14557 q = 0) : d122706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14557, d122706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14557, d122706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14558 q = 0) : d122707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14558, d122707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14558, d122707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14559 q = 0) : d122708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14559, d122708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9460 q selected
    | true =>
      simp only [d14559, d122708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro345 q selected
  have h5 (q : Pattern) (selected : d14560 q = 0) : d122709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14560, d122709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14560, d122709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14561 q = 0) : d122710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14561, d122710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14561, d122710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14562 q = 0) : d122711 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14562, d122711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14562, d122711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14563 q = 0) : d122712 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14563, d122712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14563, d122712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14564 q = 0) : d122713 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14564, d122713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14564, d122713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14565 q = 0) : d122714 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14565, d122714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14565, d122714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9462 (p : Pattern) (selected : d14569 p = 0) : d122718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14559 q = 0) : d122708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14559, d122708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9460 q selected
    | true =>
      simp only [d14559, d122708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro345 q selected
  have h2 (q : Pattern) (selected : d14560 q = 0) : d122709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14560, d122709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14560, d122709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14561 q = 0) : d122710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14561, d122710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14561, d122710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14563 q = 0) : d122712 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14563, d122712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14563, d122712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14568 q = 0) : d122717 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14568, d122717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14568, d122717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14569 q = 0) : d122718 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14569, d122718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14569, d122718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9463 (p : Pattern) (selected : d14575 p = 0) : d122724 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14566 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14566, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9461 q selected
    | true =>
      simp only [d14566, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14567 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14567, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14567, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14570 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14570, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9462 q selected
    | true =>
      simp only [d14570, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14571 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14571, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14571, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14572 q = 0) : d122721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14572, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14572, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14573 q = 0) : d122722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14573, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14573, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14574 q = 0) : d122723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14574, d122723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14574, d122723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14575 q = 0) : d122724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14575, d122724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14575, d122724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro9464 (p : Pattern) (selected : d14579 p = 0) : d122728 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14570 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14570, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9462 q selected
    | true =>
      simp only [d14570, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14571 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14571, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14571, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14576 q = 0) : d122725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14576, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14576, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14577 q = 0) : d122726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14577, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14577, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14578 q = 0) : d122727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14578, d122727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14578, d122727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14579 q = 0) : d122728 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14579, d122728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14579, d122728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9465 (p : Pattern) (selected : d14585 p = 0) : d122791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14478 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9443 q selected
    | true =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14479 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14582 q = 0) : d122788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, d122788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14582, d122788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14583 q = 0) : d122789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, d122789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14583, d122789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14584 q = 0) : d122790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, d122790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14584, d122790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14585 q = 0) : d122791 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14585, d122791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14585, d122791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9466 (p : Pattern) (selected : d14591 p = 0) : d122797 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14515 q = 0) : d122752 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, d122752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9451 q selected
    | true =>
      simp only [d14515, d122752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9452 q selected
  have h2 (q : Pattern) (selected : d14516 q = 0) : d122753 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, d122753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14516, d122753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14517 q = 0) : d122754 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, d122754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14517, d122754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14518 q = 0) : d122755 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, d122755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14518, d122755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14525 q = 0) : d122762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, d122762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9453 q selected
    | true =>
      simp only [d14525, d122762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9454 q selected
  have h6 (q : Pattern) (selected : d14526 q = 0) : d122763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, d122763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14526, d122763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14527 q = 0) : d122764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, d122764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14527, d122764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14549 q = 0) : d122786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, d122786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9458 q selected
    | true =>
      simp only [d14549, d122786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9445 q selected
  have h9 (q : Pattern) (selected : d14580 q = 0) : d122729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14580, d122729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9463 q selected
    | true =>
      simp only [d14580, d122729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9464 q selected
  have h10 (q : Pattern) (selected : d14581 q = 0) : d122787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14581, d122787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14581, d122787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14586 q = 0) : d122792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, d122792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9465 q selected
    | true =>
      simp only [d14586, d122792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d14587 q = 0) : d122793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, d122793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d14587, d122793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14588 q = 0) : d122794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14588, d122794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14588, d122794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14589 q = 0) : d122795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14589, d122795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14589, d122795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14590 q = 0) : d122796 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14590, d122796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14590, d122796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14591 q = 0) : d122797 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14591, d122797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14591, d122797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro9467 (p : Pattern) (selected : d14592 p = 0) : d122798 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14478 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9443 q selected
    | true =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14479 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14484 q = 0) : d122721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14485 q = 0) : d122722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14485, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14511 q = 0) : d122748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, d122748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14511, d122748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14592 q = 0) : d122798 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14592, d122798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14592, d122798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9468 (p : Pattern) (selected : d14593 p = 0) : d122799 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14488 q = 0) : d122725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14489 q = 0) : d122726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14489, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14513 q = 0) : d122750 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, d122750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14513, d122750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14593 q = 0) : d122799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14593, d122799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14593, d122799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9469 (p : Pattern) (selected : d14598 p = 0) : d122804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14478 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9443 q selected
    | true =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14479 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14484 q = 0) : d122721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14484, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14519 q = 0) : d122756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, d122756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14519, d122756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14520 q = 0) : d122757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, d122757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14520, d122757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14598 q = 0) : d122804 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14598, d122804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14598, d122804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9470 (p : Pattern) (selected : d14599 p = 0) : d122805 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14482 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9444 q selected
    | true =>
      simp only [d14482, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14483 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14483, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14488 q = 0) : d122725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14488, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14522 q = 0) : d122759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, d122759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14522, d122759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14523 q = 0) : d122760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, d122760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14523, d122760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14599 q = 0) : d122805 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14599, d122805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14599, d122805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9471 (p : Pattern) (selected : d14603 p = 0) : d122809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14543 q = 0) : d122780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, d122780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9457 q selected
    | true =>
      simp only [d14543, d122780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14544 q = 0) : d122781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, d122781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14544, d122781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14478 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9443 q selected
    | true =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14479 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14545 q = 0) : d122782 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, d122782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14545, d122782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14546 q = 0) : d122783 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, d122783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14546, d122783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14547 q = 0) : d122784 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, d122784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14547, d122784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14603 q = 0) : d122809 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14603, d122809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14603, d122809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9472 (p : Pattern) (selected : d14605 p = 0) : d122737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14566 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14566, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9461 q selected
    | true =>
      simp only [d14566, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14567 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14567, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14567, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14570 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14570, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9462 q selected
    | true =>
      simp only [d14570, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14571 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14571, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14571, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14572 q = 0) : d122721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14572, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14572, d122721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14573 q = 0) : d122722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14573, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14573, d122722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14574 q = 0) : d122723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14574, d122723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14574, d122723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14605 q = 0) : d122737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14605, d122737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14605, d122737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9473 (p : Pattern) (selected : d14606 p = 0) : d122738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14570 q = 0) : d122719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14570, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9462 q selected
    | true =>
      simp only [d14570, d122719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14571 q = 0) : d122720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14571, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14571, d122720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14576 q = 0) : d122725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14576, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14576, d122725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14577 q = 0) : d122726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14577, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14577, d122726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14578 q = 0) : d122727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14578, d122727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14578, d122727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14606 q = 0) : d122738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14606, d122738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14606, d122738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9474 (p : Pattern) (selected : d14609 p = 0) : d122812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14478 q = 0) : d122715 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9443 q selected
    | true =>
      simp only [d14478, d122715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14479 q = 0) : d122716 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14479, d122716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14582 q = 0) : d122788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, d122788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14582, d122788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14583 q = 0) : d122789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, d122789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14583, d122789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14584 q = 0) : d122790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, d122790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14584, d122790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14609 q = 0) : d122812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14609, d122812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14609, d122812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9475 (p : Pattern) (selected : d14615 p = 0) : d122818 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14515 q = 0) : d122752 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, d122752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9451 q selected
    | true =>
      simp only [d14515, d122752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9452 q selected
  have h2 (q : Pattern) (selected : d14516 q = 0) : d122753 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, d122753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14516, d122753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14517 q = 0) : d122754 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, d122754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14517, d122754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14518 q = 0) : d122755 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, d122755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14518, d122755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14525 q = 0) : d122762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, d122762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9453 q selected
    | true =>
      simp only [d14525, d122762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9454 q selected
  have h6 (q : Pattern) (selected : d14526 q = 0) : d122763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, d122763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14526, d122763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14527 q = 0) : d122764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, d122764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14527, d122764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14549 q = 0) : d122786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, d122786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9458 q selected
    | true =>
      simp only [d14549, d122786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9445 q selected
  have h9 (q : Pattern) (selected : d14580 q = 0) : d122729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14580, d122729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9463 q selected
    | true =>
      simp only [d14580, d122729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9464 q selected
  have h10 (q : Pattern) (selected : d14581 q = 0) : d122787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14581, d122787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14581, d122787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14586 q = 0) : d122792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, d122792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9465 q selected
    | true =>
      simp only [d14586, d122792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d14587 q = 0) : d122793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, d122793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d14587, d122793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d14588 q = 0) : d122794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14588, d122794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14588, d122794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14589 q = 0) : d122795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14589, d122795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14589, d122795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14590 q = 0) : d122796 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14590, d122796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14590, d122796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14594 q = 0) : d122800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14594, d122800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9467 q selected
    | true =>
      simp only [d14594, d122800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9468 q selected
  have h17 (q : Pattern) (selected : d14595 q = 0) : d122801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14595, d122801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14595, d122801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d14596 q = 0) : d122802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14596, d122802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d14596, d122802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d14597 q = 0) : d122803 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14597, d122803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14597, d122803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d14600 q = 0) : d122806 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14600, d122806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9469 q selected
    | true =>
      simp only [d14600, d122806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9470 q selected
  have h21 (q : Pattern) (selected : d14601 q = 0) : d122807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14601, d122807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14601, d122807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d14602 q = 0) : d122808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14602, d122808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d14602, d122808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d14604 q = 0) : d122810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, d122810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9471 q selected
    | true =>
      simp only [d14604, d122810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9448 q selected
  have h24 (q : Pattern) (selected : d14607 q = 0) : d122739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14607, d122739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9472 q selected
    | true =>
      simp only [d14607, d122739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9473 q selected
  have h25 (q : Pattern) (selected : d14608 q = 0) : d122811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14608, d122811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d14608, d122811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d14610 q = 0) : d122813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, d122813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9474 q selected
    | true =>
      simp only [d14610, d122813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d14611 q = 0) : d122814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, d122814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d14611, d122814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d14612 q = 0) : d122815 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14612, d122815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d14612, d122815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d14613 q = 0) : d122816 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14613, d122816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d14613, d122816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d14614 q = 0) : d122817 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14614, d122817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d14614, d122817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d14615 q = 0) : d122818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14615, d122818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d14615, d122818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro9476 (p : Pattern) (selected : d14622 p = 0) : d122825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14492 q = 0) : d122729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d122729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9445 q selected
    | true =>
      simp only [d14492, d122729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9446 q selected
  have h2 (q : Pattern) (selected : d14493 q = 0) : d122730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d122730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14493, d122730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14494 q = 0) : d122731 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d122731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14494, d122731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14495 q = 0) : d122732 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d122732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14495, d122732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14496 q = 0) : d122733 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d122733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14496, d122733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14617 q = 0) : d122820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, d122820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9446 q selected
    | true =>
      simp only [d14617, d122820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14618 q = 0) : d122821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, d122821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14618, d122821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14619 q = 0) : d122822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, d122822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14619, d122822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14620 q = 0) : d122823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, d122823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14620, d122823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14621 q = 0) : d122824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, d122824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14621, d122824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14622 q = 0) : d122825 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14622, d122825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14622, d122825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9477 (p : Pattern) (selected : d14628 p = 0) : d122831 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14617 q = 0) : d122820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, d122820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9446 q selected
    | true =>
      simp only [d14617, d122820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14618 q = 0) : d122821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, d122821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14618, d122821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14619 q = 0) : d122822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, d122822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14619, d122822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14620 q = 0) : d122823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, d122823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14620, d122823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14621 q = 0) : d122824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, d122824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14621, d122824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14623 q = 0) : d122826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, d122826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9449 q selected
    | true =>
      simp only [d14623, d122826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14624 q = 0) : d122827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, d122827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14624, d122827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14625 q = 0) : d122828 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, d122828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14625, d122828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14626 q = 0) : d122829 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, d122829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14626, d122829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14627 q = 0) : d122830 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, d122830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14627, d122830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14628 q = 0) : d122831 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14628, d122831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14628, d122831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro9478 (p : Pattern) (selected : d14635 p = 0) : d122838 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14604 q = 0) : d122810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, d122810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9471 q selected
    | true =>
      simp only [d14604, d122810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9448 q selected
  have h2 (q : Pattern) (selected : d14607 q = 0) : d122739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14607, d122739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9472 q selected
    | true =>
      simp only [d14607, d122739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9473 q selected
  have h3 (q : Pattern) (selected : d14608 q = 0) : d122811 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14608, d122811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14608, d122811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14610 q = 0) : d122813 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, d122813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9474 q selected
    | true =>
      simp only [d14610, d122813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14611 q = 0) : d122814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, d122814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14611, d122814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14612 q = 0) : d122815 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14612, d122815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14612, d122815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14633 q = 0) : d122836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14633, d122836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14633, d122836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14634 q = 0) : d122837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14634, d122837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14634, d122837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14635 q = 0) : d122838 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14635, d122838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14635, d122838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9479 (p : Pattern) (selected : d14637 p = 0) : d122840 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14623 q = 0) : d122826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, d122826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9449 q selected
    | true =>
      simp only [d14623, d122826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14624 q = 0) : d122827 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, d122827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14624, d122827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14625 q = 0) : d122828 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, d122828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14625, d122828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14626 q = 0) : d122829 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, d122829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14626, d122829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14627 q = 0) : d122830 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, d122830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14627, d122830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14637 q = 0) : d122840 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14637, d122840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14637, d122840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9480 (p : Pattern) (selected : d14649 p = 0) : d122852 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d965 q = 0) : d52584 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
  have h2 (q : Pattern) (selected : d834 q = 0) : d52511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro335 q selected
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d966 q = 0) : d52585 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d835 q = 0) : d52512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d967 q = 0) : d52586 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d968 q = 0) : d52587 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d52587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d968, d52587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14643 q = 0) : d122846 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14643, d122846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14643, d122846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14644 q = 0) : d122847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
  have h9 (q : Pattern) (selected : d9597 q = 0) : d101177 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6642 q selected
    | true =>
      simp only [d9597, d101177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14645 q = 0) : d122848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d122848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14645, d122848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9599 q = 0) : d101179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9599, d101179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d14646 q = 0) : d122849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14646, d122849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14646, d122849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d14647 q = 0) : d122850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14647, d122850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14647, d122850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14648 q = 0) : d122851 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14648, d122851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d14648, d122851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14649 q = 0) : d122852 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14649, d122852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14649, d122852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9481 (p : Pattern) (selected : d14653 p = 0) : d122856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12858 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
  have h2 (q : Pattern) (selected : d9468 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6620 q selected
    | true =>
      simp only [d9468, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12859 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12859, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9470 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9470, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12860 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12860, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12861 q = 0) : d113217 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12861, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14371 q = 0) : d122636 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14371, d122636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14371, d122636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d971 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h9 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d972 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d973 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d974 q = 0) : d52593 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d980 q = 0) : d52599 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14653 q = 0) : d122856 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14653, d122856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14653, d122856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9482 (p : Pattern) (selected : d14658 p = 0) : d122861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d412 q = 0) : d52178 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
  have h2 (q : Pattern) (selected : d319 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro235 q selected
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d413 q = 0) : d52179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d320 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d414 q = 0) : d52180 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d415 q = 0) : d52181 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14154 q = 0) : d122464 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14154, d122464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14154, d122464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d971 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
  have h9 (q : Pattern) (selected : d751 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro317 q selected
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d972 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d752 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d973 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d974 q = 0) : d52593 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d980 q = 0) : d52599 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14658 q = 0) : d122861 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14658, d122861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14658, d122861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9483 (p : Pattern) (selected : d14667 p = 0) : d122870 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14650 q = 0) : d122853 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14650, d122853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9480 q selected
    | true =>
      simp only [d14650, d122853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9424 q selected
  have h2 (q : Pattern) (selected : d14651 q = 0) : d122854 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14651, d122854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14651, d122854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14652 q = 0) : d122855 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14652, d122855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14652, d122855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14654 q = 0) : d122857 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14654, d122857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9424 q selected
    | true =>
      simp only [d14654, d122857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9481 q selected
  have h5 (q : Pattern) (selected : d14655 q = 0) : d122858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14655, d122858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14655, d122858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14656 q = 0) : d122859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14656, d122859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14656, d122859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14657 q = 0) : d122860 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14657, d122860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14657, d122860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14659 q = 0) : d122862 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14659, d122862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9424 q selected
    | true =>
      simp only [d14659, d122862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9482 q selected
  have h9 (q : Pattern) (selected : d14660 q = 0) : d122863 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14660, d122863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14660, d122863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14661 q = 0) : d122864 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, d122864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14661, d122864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14662 q = 0) : d122865 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d122865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9482 q selected
    | true =>
      simp only [d14662, d122865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h12 (q : Pattern) (selected : d14663 q = 0) : d122866 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d122866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14663, d122866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d14664 q = 0) : d122867 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d122867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14664, d122867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14665 q = 0) : d122868 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, d122868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14665, d122868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d14666 q = 0) : d122869 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14666, d122869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14666, d122869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d14667 q = 0) : d122870 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14667, d122870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d14667, d122870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro9484 (p : Pattern) (selected : d14672 p = 0) : d122875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14659 q = 0) : d122862 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14659, d122862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9424 q selected
    | true =>
      simp only [d14659, d122862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9482 q selected
  have h2 (q : Pattern) (selected : d14660 q = 0) : d122863 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14660, d122863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14660, d122863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14661 q = 0) : d122864 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, d122864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14661, d122864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14662 q = 0) : d122865 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d122865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9482 q selected
    | true =>
      simp only [d14662, d122865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h5 (q : Pattern) (selected : d14663 q = 0) : d122866 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d122866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14663, d122866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14664 q = 0) : d122867 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d122867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14664, d122867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14665 q = 0) : d122868 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, d122868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14665, d122868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14670 q = 0) : d122873 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, d122873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14670, d122873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14671 q = 0) : d122874 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14671, d122874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14671, d122874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14672 q = 0) : d122875 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14672, d122875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14672, d122875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9485 (p : Pattern) (selected : d14678 p = 0) : d122881 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14668 q = 0) : d122871 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14668, d122871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9483 q selected
    | true =>
      simp only [d14668, d122871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14669 q = 0) : d122872 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14669, d122872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14669, d122872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14673 q = 0) : d122876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d122876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9484 q selected
    | true =>
      simp only [d14673, d122876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14674 q = 0) : d122877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d122877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14674, d122877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14675 q = 0) : d122878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14675, d122878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14675, d122878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14676 q = 0) : d122879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14676, d122879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14676, d122879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14677 q = 0) : d122880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14677, d122880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14677, d122880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14678 q = 0) : d122881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14678, d122881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14678, d122881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9486 (p : Pattern) (selected : d14680 p = 0) : d122883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14662 q = 0) : d122865 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d122865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9482 q selected
    | true =>
      simp only [d14662, d122865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h2 (q : Pattern) (selected : d14663 q = 0) : d122866 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d122866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14663, d122866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14664 q = 0) : d122867 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d122867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14664, d122867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14670 q = 0) : d122873 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, d122873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14670, d122873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14679 q = 0) : d122882 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14679, d122882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14679, d122882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14680 q = 0) : d122883 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14680, d122883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14680, d122883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9487 (p : Pattern) (selected : d14686 p = 0) : d122889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14673 q = 0) : d122876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d122876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9484 q selected
    | true =>
      simp only [d14673, d122876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14674 q = 0) : d122877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d122877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14674, d122877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14681 q = 0) : d122884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, d122884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9486 q selected
    | true =>
      simp only [d14681, d122884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14682 q = 0) : d122885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, d122885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14682, d122885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14683 q = 0) : d122886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14683, d122886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14683, d122886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14684 q = 0) : d122887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14684, d122887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14684, d122887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14685 q = 0) : d122888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14685, d122888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14685, d122888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14686 q = 0) : d122889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14686, d122889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14686, d122889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9488 (p : Pattern) (selected : d14694 p = 0) : d122637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1013 q = 0) : d52363 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1013, d52363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1013, d52363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
  have h2 (q : Pattern) (selected : d868 q = 0) : d52290 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro341 q selected
    | true =>
      simp only [d868, d52290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1014 q = 0) : d52364 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1014, d52364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1014, d52364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d869 q = 0) : d52291 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d869, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d869, d52291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1015 q = 0) : d52365 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1015, d52365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1015, d52365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1016 q = 0) : d52366 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1016, d52366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1016, d52366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14688 q = 0) : d122635 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14688, d122635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14688, d122635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14689 q = 0) : d113214 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14689, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14689, d113214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
  have h9 (q : Pattern) (selected : d9671 q = 0) : d101083 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6655 q selected
    | true =>
      simp only [d9671, d101083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14690 q = 0) : d113215 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14690, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14690, d113215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d9673 q = 0) : d101085 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9673, d101085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d14691 q = 0) : d113216 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14691, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14691, d113216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d14692 q = 0) : d113217 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14692, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14692, d113217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14693 q = 0) : d122636 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14693, d122636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d14693, d122636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14694 q = 0) : d122637 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14694, d122637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14694, d122637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9489 (p : Pattern) (selected : d14695 p = 0) : d122861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d691 q = 0) : d52178 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d691, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d691, d52178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
  have h2 (q : Pattern) (selected : d574 q = 0) : d52118 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro282 q selected
    | true =>
      simp only [d574, d52118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d692 q = 0) : d52179 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d692, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d692, d52179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d575 q = 0) : d52119 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d575, d52119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d693 q = 0) : d52180 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d693, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d693, d52180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d694 q = 0) : d52181 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d694, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d694, d52181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14403 q = 0) : d122464 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14403, d122464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14403, d122464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1018 q = 0) : d52590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, d52590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
  have h9 (q : Pattern) (selected : d874 q = 0) : d52428 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro342 q selected
    | true =>
      simp only [d874, d52428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1019 q = 0) : d52591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1019, d52591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d875 q = 0) : d52429 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d875, d52429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d1020 q = 0) : d52592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1020, d52592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d1021 q = 0) : d52593 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1021, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d1021, d52593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d1024 q = 0) : d52599 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1024, d52599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d1024, d52599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14695 q = 0) : d122861 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14695, d122861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14695, d122861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro9490 (p : Pattern) (selected : d14705 p = 0) : d122875 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14696 q = 0) : d122862 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14696, d122862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9488 q selected
    | true =>
      simp only [d14696, d122862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9489 q selected
  have h2 (q : Pattern) (selected : d14697 q = 0) : d122863 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14697, d122863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14697, d122863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14698 q = 0) : d122864 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14698, d122864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14698, d122864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14699 q = 0) : d122865 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14699, d122865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9489 q selected
    | true =>
      simp only [d14699, d122865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro374 q selected
  have h5 (q : Pattern) (selected : d14700 q = 0) : d122866 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14700, d122866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14700, d122866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14701 q = 0) : d122867 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14701, d122867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14701, d122867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14702 q = 0) : d122868 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14702, d122868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14702, d122868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14703 q = 0) : d122873 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14703, d122873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14703, d122873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d14704 q = 0) : d122874 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14704, d122874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14704, d122874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d14705 q = 0) : d122875 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14705, d122875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d14705, d122875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro9491 (p : Pattern) (selected : d14709 p = 0) : d122883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14699 q = 0) : d122865 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14699, d122865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9489 q selected
    | true =>
      simp only [d14699, d122865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro374 q selected
  have h2 (q : Pattern) (selected : d14700 q = 0) : d122866 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14700, d122866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14700, d122866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14701 q = 0) : d122867 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14701, d122867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14701, d122867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14703 q = 0) : d122873 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14703, d122873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14703, d122873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14708 q = 0) : d122882 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14708, d122882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14708, d122882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14709 q = 0) : d122883 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14709, d122883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14709, d122883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9492 (p : Pattern) (selected : d14715 p = 0) : d122889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14706 q = 0) : d122876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14706, d122876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9490 q selected
    | true =>
      simp only [d14706, d122876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14707 q = 0) : d122877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14707, d122877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14707, d122877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14710 q = 0) : d122884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14710, d122884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9491 q selected
    | true =>
      simp only [d14710, d122884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14711 q = 0) : d122885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14711, d122885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14711, d122885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14712 q = 0) : d122886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14712, d122886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14712, d122886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14713 q = 0) : d122887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14713, d122887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14713, d122887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d14714 q = 0) : d122888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14714, d122888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14714, d122888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d14715 q = 0) : d122889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14715, d122889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d14715, d122889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro9493 (p : Pattern) (selected : d14719 p = 0) : d122894 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14710 q = 0) : d122884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14710, d122884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9491 q selected
    | true =>
      simp only [d14710, d122884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14711 q = 0) : d122885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14711, d122885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14711, d122885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14716 q = 0) : d122891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14716, d122891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14716, d122891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14717 q = 0) : d122892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14717, d122892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14717, d122892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14718 q = 0) : d122893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14718, d122893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14718, d122893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14719 q = 0) : d122894 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14719, d122894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14719, d122894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9494 (p : Pattern) (selected : d14725 p = 0) : d122900 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14673 q = 0) : d122876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d122876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9484 q selected
    | true =>
      simp only [d14673, d122876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14674 q = 0) : d122877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d122877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14674, d122877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14722 q = 0) : d122897 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14722, d122897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14722, d122897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14723 q = 0) : d122898 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14723, d122898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14723, d122898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14724 q = 0) : d122899 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14724, d122899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14724, d122899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14725 q = 0) : d122900 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14725, d122900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14725, d122900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9495 (p : Pattern) (selected : d14731 p = 0) : d122906 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14687 q = 0) : d122890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14687, d122890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9485 q selected
    | true =>
      simp only [d14687, d122890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9487 q selected
  have h2 (q : Pattern) (selected : d14720 q = 0) : d122895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14720, d122895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9492 q selected
    | true =>
      simp only [d14720, d122895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9493 q selected
  have h3 (q : Pattern) (selected : d14721 q = 0) : d122896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14721, d122896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14721, d122896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14726 q = 0) : d122901 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14726, d122901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9494 q selected
    | true =>
      simp only [d14726, d122901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14727 q = 0) : d122902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14727, d122902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14727, d122902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14728 q = 0) : d122903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14728, d122903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14728, d122903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d14729 q = 0) : d122904 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14729, d122904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14729, d122904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d14730 q = 0) : d122905 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14730, d122905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14730, d122905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14731 q = 0) : d122906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14731, d122906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14731, d122906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro9496 (p : Pattern) (selected : d14736 p = 0) : d122894 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14681 q = 0) : d122884 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, d122884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9486 q selected
    | true =>
      simp only [d14681, d122884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14682 q = 0) : d122885 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, d122885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14682, d122885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14733 q = 0) : d122891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14733, d122891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14733, d122891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14734 q = 0) : d122892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14734, d122892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14734, d122892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14735 q = 0) : d122893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14735, d122893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d14735, d122893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14736 q = 0) : d122894 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14736, d122894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14736, d122894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro9497 (p : Pattern) (selected : d14742 p = 0) : d122913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14737 q = 0) : d122908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14737, d122908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9496 q selected
    | true =>
      simp only [d14737, d122908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d14738 q = 0) : d122909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14738, d122909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14738, d122909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14739 q = 0) : d122910 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14739, d122910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14739, d122910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d14740 q = 0) : d122911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14740, d122911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14740, d122911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14741 q = 0) : d122912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14741, d122912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14741, d122912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14742 q = 0) : d122913 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14742, d122913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14742, d122913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro9498 (p : Pattern) (selected : d14748 p = 0) : d122919 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14498 q = 0) : d122735 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14498, d122735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14498, d122735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9447 q selected
  have h2 (q : Pattern) (selected : d14499 q = 0) : d122736 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14499, d122736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14499, d122736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14508 q = 0) : d122745 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d122745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9447 q selected
    | true =>
      simp only [d14508, d122745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9450 q selected
  have h4 (q : Pattern) (selected : d14509 q = 0) : d122746 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d122746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14509, d122746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14510 q = 0) : d122747 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14510, d122747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d14510, d122747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14616 q = 0) : d122819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14616, d122819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9466 q selected
    | true =>
      simp only [d14616, d122819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9475 q selected
  have h7 (q : Pattern) (selected : d14629 q = 0) : d122832 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14629, d122832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9476 q selected
    | true =>
      simp only [d14629, d122832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9477 q selected
  have h8 (q : Pattern) (selected : d14630 q = 0) : d122833 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14630, d122833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d14630, d122833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d14631 q = 0) : d122834 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14631, d122834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d14631, d122834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d14632 q = 0) : d122835 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14632, d122835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14632, d122835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d14636 q = 0) : d122839 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14636, d122839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14636, d122839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9478 q selected
  have h12 (q : Pattern) (selected : d14638 q = 0) : d122841 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14638, d122841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14638, d122841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9479 q selected
  have h13 (q : Pattern) (selected : d14639 q = 0) : d122842 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14639, d122842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d14639, d122842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14640 q = 0) : d122843 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14640, d122843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d14640, d122843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d14641 q = 0) : d122844 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14641, d122844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d14641, d122844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d14642 q = 0) : d122845 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d14642, d122845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d14642, d122845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d14732 q = 0) : d122907 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14732, d122907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14732, d122907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9495 q selected
  have h18 (q : Pattern) (selected : d14743 q = 0) : d122914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14743, d122914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14743, d122914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9497 q selected
  have h19 (q : Pattern) (selected : d14744 q = 0) : d122915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14744, d122915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d14744, d122915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d14745 q = 0) : d122916 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14745, d122916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d14745, d122916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d14746 q = 0) : d122917 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d14746, d122917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d14746, d122917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d14747 q = 0) : d122918 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d14747, d122918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d14747, d122918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d14748 q = 0) : d122919 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d14748, d122919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d14748, d122919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro9499 (p : Pattern) (selected : d14754 p = 0) : d122925 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d14749 q = 0) : d122920 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d14749, d122920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14749, d122920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9498 q selected
  have h2 (q : Pattern) (selected : d14750 q = 0) : d122921 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d14750, d122921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14750, d122921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d14751 q = 0) : d122922 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d14751, d122922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14751, d122922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14752 q = 0) : d122923 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d14752, d122923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14752, d122923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d14753 q = 0) : d122924 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d14753, d122924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14753, d122924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14754 q = 0) : d122925 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d14754, d122925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14754, d122925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
