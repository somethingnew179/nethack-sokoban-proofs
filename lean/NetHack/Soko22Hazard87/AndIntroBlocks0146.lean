import NetHack.Soko22Hazard87.AndIntroBlocks0145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro36500 (p : Pattern) (ha : d92648 p = 1) (hb : d124287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36493 q ha hb
    | true =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92626 q = 1) (hb : d124260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92626, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92626, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92647 q = 1) (hb : d124286 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92647, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92647, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92648 q = 1) (hb : d124287 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92648, d124287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92648, d124287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36501 (p : Pattern) (ha : d92655 p = 1) (hb : d124296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36493 q ha hb
    | true =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92653 q = 1) (hb : d124294 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92653, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92653, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92654 q = 1) (hb : d124295 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92654, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92654, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92655 q = 1) (hb : d124296 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92655, d124296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92655, d124296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36502 (p : Pattern) (ha : d81665 p = 1) (hb : d124252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52436 q = 1) (hb : d124118 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52436, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36492 q ha hb
    | true =>
      simp only [d52436, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36482 q ha hb
  have h2 (q : Pattern) (ha : d52437 q = 1) (hb : d124119 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52437, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52437, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52438 q = 1) (hb : d124120 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52438, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52438, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81663 q = 1) (hb : d124121 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81663, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81663, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69007 q = 1) (hb : d124247 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69007, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34839 q ha hb
    | true =>
      simp only [d69007, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h6 (q : Pattern) (ha : d69008 q = 1) (hb : d124248 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69008, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69008, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69009 q = 1) (hb : d124249 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69009, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69009, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69010 q = 1) (hb : d124250 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69010, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69010, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d81664 q = 1) (hb : d124251 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81664, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81664, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81665 q = 1) (hb : d124252 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81665, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81665, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36503 (p : Pattern) (ha : d52516 p = 1) (hb : d124303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d52513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d52513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d52514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d52514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14528 q = 1) (hb : d52515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14528, d52515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14528, d52515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52516 q = 1) (hb : d124303 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52516, d124303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52516, d124303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36504 (p : Pattern) (ha : d92661 p = 1) (hb : d124309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52517 q = 1) (hb : d124304 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52517, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36503 q ha hb
    | true =>
      simp only [d52517, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36492 q ha hb
  have h2 (q : Pattern) (ha : d52518 q = 1) (hb : d124305 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52518, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52518, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52519 q = 1) (hb : d124306 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52519, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52519, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92659 q = 1) (hb : d124307 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d92659, d124307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92659, d124307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52436 q = 1) (hb : d124118 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52436, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36492 q ha hb
    | true =>
      simp only [d52436, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36482 q ha hb
  have h6 (q : Pattern) (ha : d52437 q = 1) (hb : d124119 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52437, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52437, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52438 q = 1) (hb : d124120 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52438, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52438, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81663 q = 1) (hb : d124121 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81663, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81663, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92660 q = 1) (hb : d124308 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92660, d124308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92660, d124308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92661 q = 1) (hb : d124309 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92661, d124309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92661, d124309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36505 (p : Pattern) (ha : d92667 p = 1) (hb : d124315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92662 q = 1) (hb : d124310 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92662, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36504 q ha hb
    | true =>
      simp only [d92662, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92663 q = 1) (hb : d124311 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92663, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92663, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81666 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81666, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36502 q ha hb
    | true =>
      simp only [d81666, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81667 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81667, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81667, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92664 q = 1) (hb : d124312 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92664, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92664, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92665 q = 1) (hb : d124313 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92665, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92665, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92666 q = 1) (hb : d124314 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92666, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92666, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92667 q = 1) (hb : d124315 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92667, d124315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92667, d124315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36506 (p : Pattern) (ha : d92671 p = 1) (hb : d124262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81666 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81666, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36502 q ha hb
    | true =>
      simp only [d81666, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81667 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81667, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81667, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92668 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92668, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92668, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92669 q = 1) (hb : d124260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92669, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92669, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92670 q = 1) (hb : d124261 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92670, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92670, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92671 q = 1) (hb : d124262 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92671, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92671, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36507 (p : Pattern) (ha : d92677 p = 1) (hb : d124321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36493 q ha hb
    | true =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92674 q = 1) (hb : d124318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92674, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92674, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92675 q = 1) (hb : d124319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92675, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92675, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92676 q = 1) (hb : d124320 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92676, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92676, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92677 q = 1) (hb : d124321 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92677, d124321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92677, d124321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36508 (p : Pattern) (ha : d92683 p = 1) (hb : d124327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92649 q = 1) (hb : d124290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92649, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36500 q ha hb
    | true =>
      simp only [d92649, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36498 q ha hb
  have h2 (q : Pattern) (ha : d92650 q = 1) (hb : d124291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92650, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92650, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92651 q = 1) (hb : d124292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92651, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92651, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92652 q = 1) (hb : d124293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92652, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92652, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92656 q = 1) (hb : d124300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92656, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36501 q ha hb
    | true =>
      simp only [d92656, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36499 q ha hb
  have h6 (q : Pattern) (ha : d92657 q = 1) (hb : d124301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92657, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92657, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92658 q = 1) (hb : d124302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92658, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92658, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92672 q = 1) (hb : d124316 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92672, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36505 q ha hb
    | true =>
      simp only [d92672, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36506 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92629 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92673 q = 1) (hb : d124317 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92673, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92678 q = 1) (hb : d124322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92678, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36507 q ha hb
    | true =>
      simp only [d92678, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92679 q = 1) (hb : d124323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92679, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92679, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92680 q = 1) (hb : d124324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92680, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92681 q = 1) (hb : d124325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92681, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92682 q = 1) (hb : d124326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92682, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92683 q = 1) (hb : d124327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92683, d124327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92683, d124327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro36509 (p : Pattern) (ha : d52538 p = 1) (hb : d124329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52457 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52458 q = 1) (hb : d124264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52458, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52458, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52482 q = 1) (hb : d124288 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52482, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52482, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52538 q = 1) (hb : d124329 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52538, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52538, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36510 (p : Pattern) (ha : d52544 p = 1) (hb : d124335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52457 q = 1) (hb : d124263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52457, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52491 q = 1) (hb : d124297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52491, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52491, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52492 q = 1) (hb : d124298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52492, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52492, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52544 q = 1) (hb : d124335 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52544, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52544, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36511 (p : Pattern) (ha : d92684 p = 1) (hb : d124328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36493 q ha hb
    | true =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92626 q = 1) (hb : d124260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92626, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92626, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92647 q = 1) (hb : d124286 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92647, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92647, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92684 q = 1) (hb : d124328 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92684, d124328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92684, d124328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36512 (p : Pattern) (ha : d92689 p = 1) (hb : d124334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36493 q ha hb
    | true =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92625 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92625, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92653 q = 1) (hb : d124294 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92653, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92653, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92654 q = 1) (hb : d124295 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92654, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92654, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92689 q = 1) (hb : d124334 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92689, d124334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92689, d124334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36513 (p : Pattern) (ha : d92693 p = 1) (hb : d124339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92662 q = 1) (hb : d124310 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92662, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36504 q ha hb
    | true =>
      simp only [d92662, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92663 q = 1) (hb : d124311 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92663, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92663, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81666 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81666, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36502 q ha hb
    | true =>
      simp only [d81666, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81667 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81667, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81667, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92664 q = 1) (hb : d124312 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92664, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92664, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92665 q = 1) (hb : d124313 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92665, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92665, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92666 q = 1) (hb : d124314 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92666, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92666, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92693 q = 1) (hb : d124339 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92693, d124339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92693, d124339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36514 (p : Pattern) (ha : d92694 p = 1) (hb : d124275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81666 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81666, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36502 q ha hb
    | true =>
      simp only [d81666, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81667 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81667, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81667, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52451 q = 1) (hb : d124257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36483 q ha hb
    | true =>
      simp only [d52451, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d124258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52452, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92668 q = 1) (hb : d124259 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92668, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92668, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92669 q = 1) (hb : d124260 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92669, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92669, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92670 q = 1) (hb : d124261 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92670, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92670, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92694 q = 1) (hb : d124275 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92694, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92694, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36515 (p : Pattern) (ha : d92697 p = 1) (hb : d124342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92623 q = 1) (hb : d124253 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36493 q ha hb
    | true =>
      simp only [d92623, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92624 q = 1) (hb : d124254 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92624, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92674 q = 1) (hb : d124318 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92674, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92674, d124318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92675 q = 1) (hb : d124319 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92675, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92675, d124319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92676 q = 1) (hb : d124320 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92676, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92676, d124320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92697 q = 1) (hb : d124342 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92697, d124342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92697, d124342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36516 (p : Pattern) (ha : d92703 p = 1) (hb : d124348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92649 q = 1) (hb : d124290 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92649, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36500 q ha hb
    | true =>
      simp only [d92649, d124290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36498 q ha hb
  have h2 (q : Pattern) (ha : d92650 q = 1) (hb : d124291 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92650, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92650, d124291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92651 q = 1) (hb : d124292 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92651, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92651, d124292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92652 q = 1) (hb : d124293 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92652, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92652, d124293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92656 q = 1) (hb : d124300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92656, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36501 q ha hb
    | true =>
      simp only [d92656, d124300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36499 q ha hb
  have h6 (q : Pattern) (ha : d92657 q = 1) (hb : d124301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92657, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92657, d124301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92658 q = 1) (hb : d124302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92658, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92658, d124302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92672 q = 1) (hb : d124316 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92672, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36505 q ha hb
    | true =>
      simp only [d92672, d124316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36506 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92629 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92673 q = 1) (hb : d124317 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92673, d124317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92678 q = 1) (hb : d124322 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92678, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36507 q ha hb
    | true =>
      simp only [d92678, d124322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92679 q = 1) (hb : d124323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92679, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92679, d124323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92680 q = 1) (hb : d124324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92680, d124324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92681 q = 1) (hb : d124325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92681, d124325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92682 q = 1) (hb : d124326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92682, d124326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92685 q = 1) (hb : d124330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92685, d124330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36511 q ha hb
    | true =>
      simp only [d92685, d124330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36509 q ha hb
  have h17 (q : Pattern) (ha : d92686 q = 1) (hb : d124331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92686, d124331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92686, d124331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92687 q = 1) (hb : d124332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92687, d124332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92687, d124332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92688 q = 1) (hb : d124333 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92688, d124333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92688, d124333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92690 q = 1) (hb : d124336 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92690, d124336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36512 q ha hb
    | true =>
      simp only [d92690, d124336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36510 q ha hb
  have h21 (q : Pattern) (ha : d92691 q = 1) (hb : d124337 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92691, d124337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92691, d124337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92692 q = 1) (hb : d124338 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92692, d124338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92692, d124338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92695 q = 1) (hb : d124340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92695, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36513 q ha hb
    | true =>
      simp only [d92695, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36514 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92638 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92696 q = 1) (hb : d124341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92696, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92698 q = 1) (hb : d124343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92698, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36515 q ha hb
    | true =>
      simp only [d92698, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d92699 q = 1) (hb : d124344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92699, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d92699, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92700 q = 1) (hb : d124345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92700, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92701 q = 1) (hb : d124346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92701, d124346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92701, d124346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92702 q = 1) (hb : d124347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92702, d124347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92702, d124347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92703 q = 1) (hb : d124348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92703, d124348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92703, d124348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro36517 (p : Pattern) (ha : d92710 p = 1) (hb : d124355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92705 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92705, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36506 q ha hb
    | true =>
      simp only [d92705, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36484 q ha hb
  have h2 (q : Pattern) (ha : d92706 q = 1) (hb : d124268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92706, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92706, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92707 q = 1) (hb : d124269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92707, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92707, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92708 q = 1) (hb : d124270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92708, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92708, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92709 q = 1) (hb : d124271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92709, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92709, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52558 q = 1) (hb : d124350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52558, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36484 q ha hb
    | true =>
      simp only [d52558, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52559 q = 1) (hb : d124351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52559, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52559, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52560 q = 1) (hb : d124352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52560, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52560, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52561 q = 1) (hb : d124353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52561, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52561, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52562 q = 1) (hb : d124354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52562, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52562, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92710 q = 1) (hb : d124355 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92710, d124355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92710, d124355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36518 (p : Pattern) (ha : d92717 p = 1) (hb : d124368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92695 q = 1) (hb : d124340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92695, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36513 q ha hb
    | true =>
      simp only [d92695, d124340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36514 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92638 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92696 q = 1) (hb : d124341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92696, d124341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92698 q = 1) (hb : d124343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92698, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36515 q ha hb
    | true =>
      simp only [d92698, d124343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92699 q = 1) (hb : d124344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92699, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92699, d124344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92700 q = 1) (hb : d124345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92700, d124345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92715 q = 1) (hb : d124366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92715, d124366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92715, d124366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92716 q = 1) (hb : d124367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92716, d124367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92716, d124367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92717 q = 1) (hb : d124368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92717, d124368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92717, d124368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36519 (p : Pattern) (ha : d52595 p = 1) (hb : d124190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14370 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14370, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14370, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52595 q = 1) (hb : d124190 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52595, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52595, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36520 (p : Pattern) (ha : d81711 p = 1) (hb : d124390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52601 q = 1) (hb : d124191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52601, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36519 q ha hb
    | true =>
      simp only [d52601, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36488 q ha hb
  have h2 (q : Pattern) (ha : d52602 q = 1) (hb : d124192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52602, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52602, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52603 q = 1) (hb : d124193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52603, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52603, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81709 q = 1) (hb : d124194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81709, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81709, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d75962 q = 1) (hb : d124385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75962, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34869 q ha hb
    | true =>
      simp only [d75962, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h6 (q : Pattern) (ha : d75963 q = 1) (hb : d124386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75963, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75963, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75964 q = 1) (hb : d124387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75964, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75964, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75965 q = 1) (hb : d124388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75965, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75965, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d81710 q = 1) (hb : d124389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81710, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81710, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81711 q = 1) (hb : d124390 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81711, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81711, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36521 (p : Pattern) (ha : d52589 p = 1) (hb : d124376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d52584 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d52584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d52511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro122 q ha hb
    | true =>
      simp only [d834, d52511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d52585 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d52585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d52512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d52586 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d52586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d52587 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d52587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14643 q = 1) (hb : d52588 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14643, d52588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14643, d52588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52589 q = 1) (hb : d124376 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52589, d124376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52589, d124376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36522 (p : Pattern) (ha : d92725 p = 1) (hb : d124382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52596 q = 1) (hb : d124377 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52596, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36521 q ha hb
    | true =>
      simp only [d52596, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36519 q ha hb
  have h2 (q : Pattern) (ha : d52597 q = 1) (hb : d124378 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52597, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52597, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52598 q = 1) (hb : d124379 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52598, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52598, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92723 q = 1) (hb : d124380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d92723, d124380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92723, d124380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52601 q = 1) (hb : d124191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52601, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36519 q ha hb
    | true =>
      simp only [d52601, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36488 q ha hb
  have h6 (q : Pattern) (ha : d52602 q = 1) (hb : d124192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52602, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52602, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52603 q = 1) (hb : d124193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52603, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52603, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81709 q = 1) (hb : d124194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81709, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81709, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92724 q = 1) (hb : d124381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92724, d124381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92724, d124381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92725 q = 1) (hb : d124382 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92725, d124382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92725, d124382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36523 (p : Pattern) (ha : d92731 p = 1) (hb : d124396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92726 q = 1) (hb : d124383 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92726, d124383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36522 q ha hb
    | true =>
      simp only [d92726, d124383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92727 q = 1) (hb : d124384 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92727, d124384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92727, d124384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81712 q = 1) (hb : d124391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81712, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36520 q ha hb
    | true =>
      simp only [d81712, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81713 q = 1) (hb : d124392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81713, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81713, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92728 q = 1) (hb : d124393 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92728, d124393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92728, d124393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92729 q = 1) (hb : d124394 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92729, d124394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92729, d124394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92730 q = 1) (hb : d124395 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92730, d124395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92730, d124395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92731 q = 1) (hb : d124396 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92731, d124396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92731, d124396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36524 (p : Pattern) (ha : d92735 p = 1) (hb : d124404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81712 q = 1) (hb : d124391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81712, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36520 q ha hb
    | true =>
      simp only [d81712, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81713 q = 1) (hb : d124392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81713, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81713, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52625 q = 1) (hb : d124399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52625, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36489 q ha hb
    | true =>
      simp only [d52625, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52626 q = 1) (hb : d124400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52626, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52626, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92732 q = 1) (hb : d124401 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92732, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92732, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92733 q = 1) (hb : d124402 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92733, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92733, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92734 q = 1) (hb : d124403 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92734, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92734, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92735 q = 1) (hb : d124404 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92735, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92735, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36525 (p : Pattern) (ha : d92738 p = 1) (hb : d124390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52601 q = 1) (hb : d124191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52601, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36519 q ha hb
    | true =>
      simp only [d52601, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36488 q ha hb
  have h2 (q : Pattern) (ha : d52602 q = 1) (hb : d124192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52602, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52602, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52603 q = 1) (hb : d124193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52603, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52603, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81709 q = 1) (hb : d124194 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81709, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81709, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52606 q = 1) (hb : d124385 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52606, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36488 q ha hb
    | true =>
      simp only [d52606, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h6 (q : Pattern) (ha : d52607 q = 1) (hb : d124386 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52607, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52607, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52608 q = 1) (hb : d124387 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52608, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52608, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52614 q = 1) (hb : d124388 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52614, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52614, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92737 q = 1) (hb : d124389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92737, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92737, d124389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92738 q = 1) (hb : d124390 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92738, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92738, d124390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36526 (p : Pattern) (ha : d92750 p = 1) (hb : d124410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92739 q = 1) (hb : d124391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92739, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36525 q ha hb
    | true =>
      simp only [d92739, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92740 q = 1) (hb : d124392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92740, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92740, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92747 q = 1) (hb : d124407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92747, d124407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92747, d124407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92748 q = 1) (hb : d124408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92748, d124408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92748, d124408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92749 q = 1) (hb : d124409 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92749, d124409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92749, d124409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92750 q = 1) (hb : d124410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92750, d124410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92750, d124410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36527 (p : Pattern) (ha : d92756 p = 1) (hb : d124416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92736 q = 1) (hb : d124405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92736, d124405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36523 q ha hb
    | true =>
      simp only [d92736, d124405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36524 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92745 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92746 q = 1) (hb : d124406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92746, d124406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92746, d124406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92751 q = 1) (hb : d124411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92751, d124411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36526 q ha hb
    | true =>
      simp only [d92751, d124411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92752 q = 1) (hb : d124412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92752, d124412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92752, d124412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92753 q = 1) (hb : d124413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92753, d124413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92753, d124413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92754 q = 1) (hb : d124414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92754, d124414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92754, d124414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92755 q = 1) (hb : d124415 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92755, d124415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92755, d124415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92756 q = 1) (hb : d124416 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92756, d124416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92756, d124416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36528 (p : Pattern) (ha : d92762 p = 1) (hb : d124433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92635 q = 1) (hb : d124273 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92635, d124273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92635, d124273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36495 q ha hb
  have h2 (q : Pattern) (ha : d92636 q = 1) (hb : d124274 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92636, d124274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92636, d124274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92644 q = 1) (hb : d124283 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92644, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36495 q ha hb
    | true =>
      simp only [d92644, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36497 q ha hb
  have h4 (q : Pattern) (ha : d92645 q = 1) (hb : d124284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92645, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92645, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92646 q = 1) (hb : d124285 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92646, d124285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92646, d124285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92704 q = 1) (hb : d124349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92704, d124349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36508 q ha hb
    | true =>
      simp only [d92704, d124349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36516 q ha hb
  have h7 (q : Pattern) (ha : d92711 q = 1) (hb : d124362 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92711, d124362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36517 q ha hb
    | true =>
      simp only [d92711, d124362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36486 q ha hb
  have h8 (q : Pattern) (ha : d92712 q = 1) (hb : d124363 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92712, d124363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92712, d124363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92713 q = 1) (hb : d124364 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92713, d124364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92713, d124364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92714 q = 1) (hb : d124365 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92714, d124365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92714, d124365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92718 q = 1) (hb : d124369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92718, d124369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92718, d124369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36518 q ha hb
  have h12 (q : Pattern) (ha : d52579 q = 1) (hb : d124371 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52579, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52579, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36487 q ha hb
  have h13 (q : Pattern) (ha : d92719 q = 1) (hb : d124372 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92719, d124372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92719, d124372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92720 q = 1) (hb : d124373 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92720, d124373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92720, d124373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92721 q = 1) (hb : d124374 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92721, d124374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92721, d124374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92722 q = 1) (hb : d124375 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92722, d124375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92722, d124375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92757 q = 1) (hb : d124417 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92757, d124417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92757, d124417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36527 q ha hb
  have h18 (q : Pattern) (ha : d52651 q = 1) (hb : d124428 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52651, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52651, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36491 q ha hb
  have h19 (q : Pattern) (ha : d92758 q = 1) (hb : d124429 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92758, d124429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92758, d124429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92759 q = 1) (hb : d124430 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92759, d124430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92759, d124430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92760 q = 1) (hb : d124431 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92760, d124431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92760, d124431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92761 q = 1) (hb : d124432 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92761, d124432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92761, d124432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92762 q = 1) (hb : d124433 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92762, d124433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92762, d124433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36529 (p : Pattern) (ha : d92768 p = 1) (hb : d124439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92763 q = 1) (hb : d124434 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92763, d124434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92763, d124434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36528 q ha hb
  have h2 (q : Pattern) (ha : d92764 q = 1) (hb : d124435 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92764, d124435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92764, d124435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92765 q = 1) (hb : d124436 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92765, d124436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92765, d124436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92766 q = 1) (hb : d124437 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92766, d124437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92766, d124437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92767 q = 1) (hb : d124438 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92767, d124438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92767, d124438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92768 q = 1) (hb : d124439 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92768, d124439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92768, d124439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36530 (p : Pattern) (ha : d52709 p = 1) (hb : d124443 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14762 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14762, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14762, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52709 q = 1) (hb : d124443 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52709, d124443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52709, d124443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36531 (p : Pattern) (ha : d52733 p = 1) (hb : d124457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52723 q = 1) (hb : d124448 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52723, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36530 q ha hb
    | true =>
      simp only [d52723, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28789 q hb ha
  have h2 (q : Pattern) (ha : d52724 q = 1) (hb : d124449 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52724, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52724, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52725 q = 1) (hb : d124450 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52725, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52725, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52727 q = 1) (hb : d124451 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52727, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52727, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52732 q = 1) (hb : d124456 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52732, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52732, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52733 q = 1) (hb : d124457 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52733, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52733, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36532 (p : Pattern) (ha : d52743 p = 1) (hb : d124467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52741 q = 1) (hb : d124465 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52741, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52741, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52742 q = 1) (hb : d124466 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52742, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52742, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52743 q = 1) (hb : d124467 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52743, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52743, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36533 (p : Pattern) (ha : d52753 p = 1) (hb : d124477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52741 q = 1) (hb : d124465 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52741, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52741, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52742 q = 1) (hb : d124466 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52742, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52742, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52753 q = 1) (hb : d124477 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52753, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52753, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36534 (p : Pattern) (ha : d52849 p = 1) (hb : d124580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52838 q = 1) (hb : d124569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52838, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36532 q ha hb
    | true =>
      simp only [d52838, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52839 q = 1) (hb : d124570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52839, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52839, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52840 q = 1) (hb : d124571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52840, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52840, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52841 q = 1) (hb : d124572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52841, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52841, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52842 q = 1) (hb : d124573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52842, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52842, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52844 q = 1) (hb : d124575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52844, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36533 q ha hb
    | true =>
      simp only [d52844, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52845 q = 1) (hb : d124576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52845, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52845, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52846 q = 1) (hb : d124577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52846, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52846, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52847 q = 1) (hb : d124578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52847, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52847, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52848 q = 1) (hb : d124579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52848, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52848, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52849 q = 1) (hb : d124580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52849, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52849, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36535 (p : Pattern) (ha : d52858 p = 1) (hb : d124589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52844 q = 1) (hb : d124575 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52844, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36533 q ha hb
    | true =>
      simp only [d52844, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52845 q = 1) (hb : d124576 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52845, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52845, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52846 q = 1) (hb : d124577 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52846, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52846, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52847 q = 1) (hb : d124578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52847, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52847, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52848 q = 1) (hb : d124579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52848, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52848, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52858 q = 1) (hb : d124589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52858, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52858, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36536 (p : Pattern) (ha : d52889 p = 1) (hb : d124601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15014 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15014, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15014, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52889 q = 1) (hb : d124601 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52889, d124601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52889, d124601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36537 (p : Pattern) (ha : d52918 p = 1) (hb : d124627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52900 q = 1) (hb : d124622 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52900, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36536 q ha hb
    | true =>
      simp only [d52900, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28795 q hb ha
  have h2 (q : Pattern) (ha : d52901 q = 1) (hb : d124623 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52901, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52901, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52902 q = 1) (hb : d124624 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52902, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52902, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52908 q = 1) (hb : d124625 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52908, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52908, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52917 q = 1) (hb : d124626 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52917, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52917, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52918 q = 1) (hb : d124627 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d52918, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52918, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36538 (p : Pattern) (ha : d52929 p = 1) (hb : d124654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52919 q = 1) (hb : d124628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52919, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36537 q ha hb
    | true =>
      simp only [d52919, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52920 q = 1) (hb : d124629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52920, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52920, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52926 q = 1) (hb : d124651 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52926, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52926, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52927 q = 1) (hb : d124652 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52927, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52927, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52928 q = 1) (hb : d124653 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52928, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52928, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52929 q = 1) (hb : d124654 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52929, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52929, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36539 (p : Pattern) (ha : d52944 p = 1) (hb : d124660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52939 q = 1) (hb : d124655 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52939, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36538 q ha hb
    | true =>
      simp only [d52939, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52940 q = 1) (hb : d124656 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52940, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52940, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52941 q = 1) (hb : d124657 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52941, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52941, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52942 q = 1) (hb : d124658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52942, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52942, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52943 q = 1) (hb : d124659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52943, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52943, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52944 q = 1) (hb : d124660 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52944, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52944, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36540 (p : Pattern) (ha : d52707 p = 1) (hb : d124442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14757 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14757, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14757, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52707 q = 1) (hb : d124442 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52707, d124442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52707, d124442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36541 (p : Pattern) (ha : d92772 p = 1) (hb : d124453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52710 q = 1) (hb : d124444 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52710, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36540 q ha hb
    | true =>
      simp only [d52710, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36530 q ha hb
  have h2 (q : Pattern) (ha : d52711 q = 1) (hb : d124445 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52711, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52711, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52712 q = 1) (hb : d124446 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52712, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52712, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81742 q = 1) (hb : d124447 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81742, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81742, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52723 q = 1) (hb : d124448 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52723, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36530 q ha hb
    | true =>
      simp only [d52723, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28789 q hb ha
  have h6 (q : Pattern) (ha : d52724 q = 1) (hb : d124449 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52724, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52724, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52725 q = 1) (hb : d124450 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52725, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52725, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52727 q = 1) (hb : d124451 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52727, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52727, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92771 q = 1) (hb : d124452 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92771, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92771, d124452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92772 q = 1) (hb : d124453 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92772, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92772, d124453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36542 (p : Pattern) (ha : d92778 p = 1) (hb : d124463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36541 q ha hb
    | true =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92776 q = 1) (hb : d124461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92776, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92776, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92777 q = 1) (hb : d124462 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92777, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92777, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92778 q = 1) (hb : d124463 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92778, d124463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92778, d124463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36543 (p : Pattern) (ha : d92784 p = 1) (hb : d124473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92779 q = 1) (hb : d124468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36542 q ha hb
    | true =>
      simp only [d92779, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36532 q ha hb
  have h2 (q : Pattern) (ha : d92780 q = 1) (hb : d124469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92780, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92780, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92781 q = 1) (hb : d124470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92781, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92781, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92782 q = 1) (hb : d124471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92782, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92782, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92783 q = 1) (hb : d124472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92783, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92783, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92784 q = 1) (hb : d124473 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92784, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92784, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36544 (p : Pattern) (ha : d92787 p = 1) (hb : d124476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36541 q ha hb
    | true =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92776 q = 1) (hb : d124461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92776, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92776, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92777 q = 1) (hb : d124462 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92777, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92777, d124462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92787 q = 1) (hb : d124476 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92787, d124476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92787, d124476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36545 (p : Pattern) (ha : d92793 p = 1) (hb : d124483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92779 q = 1) (hb : d124468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36542 q ha hb
    | true =>
      simp only [d92779, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36532 q ha hb
  have h2 (q : Pattern) (ha : d92780 q = 1) (hb : d124469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92780, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92780, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92781 q = 1) (hb : d124470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92781, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92781, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92782 q = 1) (hb : d124471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92782, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92782, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92783 q = 1) (hb : d124472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92783, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92783, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92788 q = 1) (hb : d124478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92788, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36544 q ha hb
    | true =>
      simp only [d92788, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36533 q ha hb
  have h7 (q : Pattern) (ha : d92789 q = 1) (hb : d124479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92789, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92789, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92790 q = 1) (hb : d124480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92790, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92790, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92791 q = 1) (hb : d124481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92791, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92791, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92792 q = 1) (hb : d124482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92792, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92792, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92793 q = 1) (hb : d124483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92793, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92793, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36546 (p : Pattern) (ha : d52766 p = 1) (hb : d124490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52741 q = 1) (hb : d124465 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52741, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52741, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52765 q = 1) (hb : d124489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52765, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52765, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52766 q = 1) (hb : d124490 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52766, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52766, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36547 (p : Pattern) (ha : d52776 p = 1) (hb : d124500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52774 q = 1) (hb : d124498 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52774, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52774, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52775 q = 1) (hb : d124499 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52775, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52775, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52776 q = 1) (hb : d124500 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52776, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52776, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36548 (p : Pattern) (ha : d92798 p = 1) (hb : d124488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36541 q ha hb
    | true =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92776 q = 1) (hb : d124461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92776, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92776, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92797 q = 1) (hb : d124487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92797, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92797, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92798 q = 1) (hb : d124488 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92798, d124488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92798, d124488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36549 (p : Pattern) (ha : d92805 p = 1) (hb : d124497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36541 q ha hb
    | true =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92803 q = 1) (hb : d124495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92803, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92803, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92804 q = 1) (hb : d124496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92804, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92804, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92805 q = 1) (hb : d124497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92805, d124497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92805, d124497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36550 (p : Pattern) (ha : d81744 p = 1) (hb : d124518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52710 q = 1) (hb : d124444 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52710, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36540 q ha hb
    | true =>
      simp only [d52710, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36530 q ha hb
  have h2 (q : Pattern) (ha : d52711 q = 1) (hb : d124445 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52711, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52711, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52712 q = 1) (hb : d124446 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52712, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52712, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81742 q = 1) (hb : d124447 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81742, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81742, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69114 q = 1) (hb : d124513 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69114, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34883 q ha hb
    | true =>
      simp only [d69114, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7948 q hb ha
  have h6 (q : Pattern) (ha : d69115 q = 1) (hb : d124514 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69115, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69115, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69116 q = 1) (hb : d124515 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69116, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69116, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69117 q = 1) (hb : d124516 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69117, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69117, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d81743 q = 1) (hb : d124517 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81743, d124517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81743, d124517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81744 q = 1) (hb : d124518 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81744, d124518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81744, d124518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36551 (p : Pattern) (ha : d52796 p = 1) (hb : d124504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1212 q = 1) (hb : d52793 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1212, d52793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1213 q = 1) (hb : d52794 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1213, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1213, d52794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14835 q = 1) (hb : d52795 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14835, d52795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14835, d52795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52796 q = 1) (hb : d124504 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52796, d124504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52796, d124504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36552 (p : Pattern) (ha : d92811 p = 1) (hb : d124510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52797 q = 1) (hb : d124505 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52797, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36551 q ha hb
    | true =>
      simp only [d52797, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36540 q ha hb
  have h2 (q : Pattern) (ha : d52798 q = 1) (hb : d124506 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52798, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52798, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52799 q = 1) (hb : d124507 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52799, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52799, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92809 q = 1) (hb : d124508 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d92809, d124508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92809, d124508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52710 q = 1) (hb : d124444 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52710, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36540 q ha hb
    | true =>
      simp only [d52710, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36530 q ha hb
  have h6 (q : Pattern) (ha : d52711 q = 1) (hb : d124445 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52711, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52711, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52712 q = 1) (hb : d124446 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52712, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52712, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81742 q = 1) (hb : d124447 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81742, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81742, d124447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92810 q = 1) (hb : d124509 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92810, d124509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92810, d124509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92811 q = 1) (hb : d124510 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92811, d124510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92811, d124510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36553 (p : Pattern) (ha : d92817 p = 1) (hb : d124524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92812 q = 1) (hb : d124511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92812, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36552 q ha hb
    | true =>
      simp only [d92812, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92813 q = 1) (hb : d124512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92813, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92813, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81745 q = 1) (hb : d124519 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81745, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36550 q ha hb
    | true =>
      simp only [d81745, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81746 q = 1) (hb : d124520 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81746, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81746, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92814 q = 1) (hb : d124521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92814, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92814, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92815 q = 1) (hb : d124522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92815, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92815, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92816 q = 1) (hb : d124523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92816, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92816, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92817 q = 1) (hb : d124524 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92817, d124524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92817, d124524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36554 (p : Pattern) (ha : d92821 p = 1) (hb : d124528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81745 q = 1) (hb : d124519 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81745, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36550 q ha hb
    | true =>
      simp only [d81745, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81746 q = 1) (hb : d124520 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81746, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81746, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92818 q = 1) (hb : d124525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92818, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92818, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92819 q = 1) (hb : d124526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92819, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92819, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92820 q = 1) (hb : d124527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92820, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92820, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92821 q = 1) (hb : d124528 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92821, d124528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92821, d124528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36555 (p : Pattern) (ha : d92827 p = 1) (hb : d124534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36541 q ha hb
    | true =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92824 q = 1) (hb : d124531 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92824, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92824, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92825 q = 1) (hb : d124532 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92825, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92825, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92826 q = 1) (hb : d124533 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92826, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92826, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92827 q = 1) (hb : d124534 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92827, d124534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92827, d124534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36556 (p : Pattern) (ha : d92833 p = 1) (hb : d124540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92799 q = 1) (hb : d124491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92799, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36548 q ha hb
    | true =>
      simp only [d92799, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36546 q ha hb
  have h2 (q : Pattern) (ha : d92800 q = 1) (hb : d124492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92800, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92800, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92801 q = 1) (hb : d124493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92801, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92801, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92802 q = 1) (hb : d124494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92802, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92802, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92806 q = 1) (hb : d124501 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92806, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36549 q ha hb
    | true =>
      simp only [d92806, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36547 q ha hb
  have h6 (q : Pattern) (ha : d92807 q = 1) (hb : d124502 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92807, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92807, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92808 q = 1) (hb : d124503 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92808, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92808, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92822 q = 1) (hb : d124529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92822, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36553 q ha hb
    | true =>
      simp only [d92822, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36554 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92823 q = 1) (hb : d124530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92823, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92828 q = 1) (hb : d124535 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92828, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36555 q ha hb
    | true =>
      simp only [d92828, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92829 q = 1) (hb : d124536 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92829, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92829, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92830 q = 1) (hb : d124537 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92830, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92831 q = 1) (hb : d124538 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92831, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92832 q = 1) (hb : d124539 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92832, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92833 q = 1) (hb : d124540 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92833, d124540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92833, d124540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro36557 (p : Pattern) (ha : d52818 p = 1) (hb : d124542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52741 q = 1) (hb : d124465 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52741, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52741, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52765 q = 1) (hb : d124489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52765, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52765, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52818 q = 1) (hb : d124542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52818, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52818, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36558 (p : Pattern) (ha : d52824 p = 1) (hb : d124548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52740 q = 1) (hb : d124464 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52740, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52774 q = 1) (hb : d124498 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d52774, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52774, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52775 q = 1) (hb : d124499 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d52775, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52775, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d52824 q = 1) (hb : d124548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d52824, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52824, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36559 (p : Pattern) (ha : d92834 p = 1) (hb : d124541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36541 q ha hb
    | true =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92776 q = 1) (hb : d124461 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92776, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92776, d124461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92797 q = 1) (hb : d124487 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92797, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92797, d124487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92834 q = 1) (hb : d124541 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92834, d124541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92834, d124541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36560 (p : Pattern) (ha : d92839 p = 1) (hb : d124547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36541 q ha hb
    | true =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92775 q = 1) (hb : d124460 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92775, d124460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92803 q = 1) (hb : d124495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92803, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92803, d124495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92804 q = 1) (hb : d124496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92804, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92804, d124496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92839 q = 1) (hb : d124547 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92839, d124547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92839, d124547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36561 (p : Pattern) (ha : d92843 p = 1) (hb : d124552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92812 q = 1) (hb : d124511 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92812, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36552 q ha hb
    | true =>
      simp only [d92812, d124511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92813 q = 1) (hb : d124512 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92813, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92813, d124512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81745 q = 1) (hb : d124519 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81745, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36550 q ha hb
    | true =>
      simp only [d81745, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81746 q = 1) (hb : d124520 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81746, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81746, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92814 q = 1) (hb : d124521 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92814, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92814, d124521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92815 q = 1) (hb : d124522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92815, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92815, d124522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92816 q = 1) (hb : d124523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92816, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92816, d124523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92843 q = 1) (hb : d124552 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92843, d124552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92843, d124552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36562 (p : Pattern) (ha : d92844 p = 1) (hb : d124553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81745 q = 1) (hb : d124519 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81745, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36550 q ha hb
    | true =>
      simp only [d81745, d124519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81746 q = 1) (hb : d124520 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81746, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81746, d124520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52734 q = 1) (hb : d124458 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36531 q ha hb
    | true =>
      simp only [d52734, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d124459 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52735, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92818 q = 1) (hb : d124525 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92818, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92818, d124525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92819 q = 1) (hb : d124526 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92819, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92819, d124526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92820 q = 1) (hb : d124527 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92820, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92820, d124527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92844 q = 1) (hb : d124553 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92844, d124553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92844, d124553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36563 (p : Pattern) (ha : d92847 p = 1) (hb : d124556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92773 q = 1) (hb : d124454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36541 q ha hb
    | true =>
      simp only [d92773, d124454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92774 q = 1) (hb : d124455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92774, d124455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92824 q = 1) (hb : d124531 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92824, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92824, d124531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92825 q = 1) (hb : d124532 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92825, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92825, d124532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92826 q = 1) (hb : d124533 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92826, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92826, d124533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92847 q = 1) (hb : d124556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92847, d124556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92847, d124556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36564 (p : Pattern) (ha : d92853 p = 1) (hb : d124562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92799 q = 1) (hb : d124491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92799, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36548 q ha hb
    | true =>
      simp only [d92799, d124491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36546 q ha hb
  have h2 (q : Pattern) (ha : d92800 q = 1) (hb : d124492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92800, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92800, d124492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92801 q = 1) (hb : d124493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92801, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92801, d124493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92802 q = 1) (hb : d124494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92802, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92802, d124494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92806 q = 1) (hb : d124501 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92806, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36549 q ha hb
    | true =>
      simp only [d92806, d124501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36547 q ha hb
  have h6 (q : Pattern) (ha : d92807 q = 1) (hb : d124502 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92807, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92807, d124502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92808 q = 1) (hb : d124503 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92808, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92808, d124503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92822 q = 1) (hb : d124529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92822, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36553 q ha hb
    | true =>
      simp only [d92822, d124529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36554 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92779 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92823 q = 1) (hb : d124530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92823, d124530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92828 q = 1) (hb : d124535 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92828, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36555 q ha hb
    | true =>
      simp only [d92828, d124535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92829 q = 1) (hb : d124536 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92829, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92829, d124536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92830 q = 1) (hb : d124537 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92830, d124537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92831 q = 1) (hb : d124538 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92831, d124538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92832 q = 1) (hb : d124539 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92832, d124539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92835 q = 1) (hb : d124543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92835, d124543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36559 q ha hb
    | true =>
      simp only [d92835, d124543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36557 q ha hb
  have h17 (q : Pattern) (ha : d92836 q = 1) (hb : d124544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92836, d124544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92836, d124544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92837 q = 1) (hb : d124545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92837, d124545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92837, d124545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92838 q = 1) (hb : d124546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92838, d124546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92838, d124546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92840 q = 1) (hb : d124549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92840, d124549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36560 q ha hb
    | true =>
      simp only [d92840, d124549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36558 q ha hb
  have h21 (q : Pattern) (ha : d92841 q = 1) (hb : d124550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92841, d124550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92841, d124550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92842 q = 1) (hb : d124551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92842, d124551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92842, d124551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92845 q = 1) (hb : d124554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92845, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36561 q ha hb
    | true =>
      simp only [d92845, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36562 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92788 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92846 q = 1) (hb : d124555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92846, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92848 q = 1) (hb : d124557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92848, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36563 q ha hb
    | true =>
      simp only [d92848, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d92849 q = 1) (hb : d124558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92849, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d92849, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92850 q = 1) (hb : d124559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92850, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92851 q = 1) (hb : d124560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92851, d124560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92851, d124560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92852 q = 1) (hb : d124561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92852, d124561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92852, d124561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92853 q = 1) (hb : d124562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92853, d124562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92853, d124562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro36565 (p : Pattern) (ha : d92860 p = 1) (hb : d124574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92855 q = 1) (hb : d124564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92855, d124564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36554 q ha hb
    | true =>
      simp only [d92855, d124564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36532 q ha hb
  have h2 (q : Pattern) (ha : d92856 q = 1) (hb : d124565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92856, d124565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92856, d124565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92857 q = 1) (hb : d124566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92857, d124566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92857, d124566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92858 q = 1) (hb : d124567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92858, d124567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92858, d124567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92859 q = 1) (hb : d124568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92859, d124568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92859, d124568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52838 q = 1) (hb : d124569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52838, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36532 q ha hb
    | true =>
      simp only [d52838, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52839 q = 1) (hb : d124570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52839, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52839, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52840 q = 1) (hb : d124571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52840, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52840, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52841 q = 1) (hb : d124572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d52841, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52841, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52842 q = 1) (hb : d124573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d52842, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52842, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92860 q = 1) (hb : d124574 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92860, d124574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92860, d124574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36566 (p : Pattern) (ha : d92867 p = 1) (hb : d124587 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92845 q = 1) (hb : d124554 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92845, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36561 q ha hb
    | true =>
      simp only [d92845, d124554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36562 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92788 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92846 q = 1) (hb : d124555 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92846, d124555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92848 q = 1) (hb : d124557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92848, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36563 q ha hb
    | true =>
      simp only [d92848, d124557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92849 q = 1) (hb : d124558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92849, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92849, d124558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92850 q = 1) (hb : d124559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92850, d124559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92865 q = 1) (hb : d124585 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92865, d124585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92865, d124585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92866 q = 1) (hb : d124586 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92866, d124586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92866, d124586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92867 q = 1) (hb : d124587 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92867, d124587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92867, d124587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36567 (p : Pattern) (ha : d52884 p = 1) (hb : d124596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1382 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1383 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14993 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14993, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14993, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52884 q = 1) (hb : d124596 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52884, d124596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52884, d124596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36568 (p : Pattern) (ha : d81790 p = 1) (hb : d124615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52890 q = 1) (hb : d124602 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52890, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36567 q ha hb
    | true =>
      simp only [d52890, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36536 q ha hb
  have h2 (q : Pattern) (ha : d52891 q = 1) (hb : d124603 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52891, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52891, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52892 q = 1) (hb : d124604 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52892, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52892, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81788 q = 1) (hb : d124605 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81788, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81788, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76096 q = 1) (hb : d124610 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76096, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34917 q ha hb
    | true =>
      simp only [d76096, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10887 q hb ha
  have h6 (q : Pattern) (ha : d76097 q = 1) (hb : d124611 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76097, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76097, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76098 q = 1) (hb : d124612 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76098, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76098, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76099 q = 1) (hb : d124613 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76099, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76099, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d81789 q = 1) (hb : d124614 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81789, d124614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81789, d124614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81790 q = 1) (hb : d124615 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81790, d124615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81790, d124615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36569 (p : Pattern) (ha : d52878 p = 1) (hb : d124595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1376 q = 1) (hb : d52864 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d52864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
  have h2 (q : Pattern) (ha : d1210 q = 1) (hb : d52791 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro174 q ha hb
    | true =>
      simp only [d1210, d52791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1377 q = 1) (hb : d52865 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1377, d52865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1211 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1211, d52792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1378 q = 1) (hb : d52866 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1378, d52866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1379 q = 1) (hb : d52867 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1379, d52867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14986 q = 1) (hb : d52872 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14986, d52872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14986, d52872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d52878 q = 1) (hb : d124595 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52878, d124595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d52878, d124595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36570 (p : Pattern) (ha : d92875 p = 1) (hb : d124607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52885 q = 1) (hb : d124597 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52885, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36569 q ha hb
    | true =>
      simp only [d52885, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36567 q ha hb
  have h2 (q : Pattern) (ha : d52886 q = 1) (hb : d124598 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52886, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52886, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52887 q = 1) (hb : d124599 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52887, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52887, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92873 q = 1) (hb : d124600 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d92873, d124600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92873, d124600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52890 q = 1) (hb : d124602 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52890, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36567 q ha hb
    | true =>
      simp only [d52890, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36536 q ha hb
  have h6 (q : Pattern) (ha : d52891 q = 1) (hb : d124603 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52891, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52891, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52892 q = 1) (hb : d124604 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52892, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52892, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81788 q = 1) (hb : d124605 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81788, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81788, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92874 q = 1) (hb : d124606 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92874, d124606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92874, d124606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92875 q = 1) (hb : d124607 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92875, d124607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92875, d124607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36571 (p : Pattern) (ha : d92881 p = 1) (hb : d124621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92876 q = 1) (hb : d124608 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92876, d124608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36570 q ha hb
    | true =>
      simp only [d92876, d124608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92877 q = 1) (hb : d124609 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92877, d124609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92877, d124609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81791 q = 1) (hb : d124616 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81791, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36568 q ha hb
    | true =>
      simp only [d81791, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81792 q = 1) (hb : d124617 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81792, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81792, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92878 q = 1) (hb : d124618 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92878, d124618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92878, d124618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92879 q = 1) (hb : d124619 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92879, d124619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92879, d124619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92880 q = 1) (hb : d124620 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92880, d124620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92880, d124620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92881 q = 1) (hb : d124621 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92881, d124621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92881, d124621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36572 (p : Pattern) (ha : d92885 p = 1) (hb : d124633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81791 q = 1) (hb : d124616 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81791, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36568 q ha hb
    | true =>
      simp only [d81791, d124616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81792 q = 1) (hb : d124617 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81792, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81792, d124617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52919 q = 1) (hb : d124628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52919, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36537 q ha hb
    | true =>
      simp only [d52919, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52920 q = 1) (hb : d124629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52920, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52920, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92882 q = 1) (hb : d124630 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92882, d124630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92882, d124630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92883 q = 1) (hb : d124631 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92883, d124631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92883, d124631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92884 q = 1) (hb : d124632 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92884, d124632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92884, d124632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92885 q = 1) (hb : d124633 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92885, d124633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92885, d124633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36573 (p : Pattern) (ha : d92888 p = 1) (hb : d124637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52890 q = 1) (hb : d124602 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52890, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36567 q ha hb
    | true =>
      simp only [d52890, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36536 q ha hb
  have h2 (q : Pattern) (ha : d52891 q = 1) (hb : d124603 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52891, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52891, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52892 q = 1) (hb : d124604 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52892, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52892, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81788 q = 1) (hb : d124605 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81788, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81788, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52900 q = 1) (hb : d124622 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52900, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36536 q ha hb
    | true =>
      simp only [d52900, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28795 q hb ha
  have h6 (q : Pattern) (ha : d52901 q = 1) (hb : d124623 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52901, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52901, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52902 q = 1) (hb : d124624 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52902, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52902, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52908 q = 1) (hb : d124625 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52908, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52908, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92887 q = 1) (hb : d124636 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92887, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92887, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92888 q = 1) (hb : d124637 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92888, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92888, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36574 (p : Pattern) (ha : d92900 p = 1) (hb : d124643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92889 q = 1) (hb : d124638 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92889, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36573 q ha hb
    | true =>
      simp only [d92889, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92890 q = 1) (hb : d124639 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92890, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92890, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92897 q = 1) (hb : d124640 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92897, d124640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92897, d124640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92898 q = 1) (hb : d124641 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92898, d124641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92898, d124641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92899 q = 1) (hb : d124642 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92899, d124642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92899, d124642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92900 q = 1) (hb : d124643 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92900, d124643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92900, d124643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36575 (p : Pattern) (ha : d92906 p = 1) (hb : d124649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92886 q = 1) (hb : d124634 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92886, d124634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36571 q ha hb
    | true =>
      simp only [d92886, d124634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36572 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92895 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92896 q = 1) (hb : d124635 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92896, d124635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92896, d124635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92901 q = 1) (hb : d124644 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92901, d124644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36574 q ha hb
    | true =>
      simp only [d92901, d124644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92902 q = 1) (hb : d124645 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92902, d124645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92902, d124645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92903 q = 1) (hb : d124646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92903, d124646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92903, d124646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92904 q = 1) (hb : d124647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92904, d124647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92904, d124647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92905 q = 1) (hb : d124648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92905, d124648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92905, d124648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92906 q = 1) (hb : d124649 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92906, d124649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92906, d124649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36576 (p : Pattern) (ha : d92912 p = 1) (hb : d124666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92785 q = 1) (hb : d124474 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92785, d124474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92785, d124474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36543 q ha hb
  have h2 (q : Pattern) (ha : d92786 q = 1) (hb : d124475 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92786, d124475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92786, d124475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92794 q = 1) (hb : d124484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92794, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36543 q ha hb
    | true =>
      simp only [d92794, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36545 q ha hb
  have h4 (q : Pattern) (ha : d92795 q = 1) (hb : d124485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92795, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92795, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92796 q = 1) (hb : d124486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92796, d124486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92796, d124486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92854 q = 1) (hb : d124563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92854, d124563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36556 q ha hb
    | true =>
      simp only [d92854, d124563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36564 q ha hb
  have h7 (q : Pattern) (ha : d92861 q = 1) (hb : d124581 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92861, d124581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36565 q ha hb
    | true =>
      simp only [d92861, d124581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36534 q ha hb
  have h8 (q : Pattern) (ha : d92862 q = 1) (hb : d124582 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92862, d124582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92862, d124582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92863 q = 1) (hb : d124583 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92863, d124583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92863, d124583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92864 q = 1) (hb : d124584 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92864, d124584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92864, d124584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92868 q = 1) (hb : d124588 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92868, d124588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92868, d124588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36566 q ha hb
  have h12 (q : Pattern) (ha : d52859 q = 1) (hb : d124590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52859, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52859, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36535 q ha hb
  have h13 (q : Pattern) (ha : d92869 q = 1) (hb : d124591 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92869, d124591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92869, d124591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92870 q = 1) (hb : d124592 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92870, d124592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92870, d124592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92871 q = 1) (hb : d124593 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92871, d124593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92871, d124593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92872 q = 1) (hb : d124594 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92872, d124594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92872, d124594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92907 q = 1) (hb : d124650 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92907, d124650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92907, d124650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36575 q ha hb
  have h18 (q : Pattern) (ha : d52945 q = 1) (hb : d124661 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52945, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52945, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36539 q ha hb
  have h19 (q : Pattern) (ha : d92908 q = 1) (hb : d124662 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92908, d124662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92908, d124662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92909 q = 1) (hb : d124663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92909, d124663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92909, d124663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92910 q = 1) (hb : d124664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92910, d124664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92910, d124664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92911 q = 1) (hb : d124665 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92911, d124665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92911, d124665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92912 q = 1) (hb : d124666 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92912, d124666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92912, d124666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36577 (p : Pattern) (ha : d92918 p = 1) (hb : d124672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92913 q = 1) (hb : d124667 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92913, d124667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92913, d124667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36576 q ha hb
  have h2 (q : Pattern) (ha : d92914 q = 1) (hb : d124668 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92914, d124668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92914, d124668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92915 q = 1) (hb : d124669 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92915, d124669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92915, d124669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92916 q = 1) (hb : d124670 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92916, d124670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92916, d124670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92917 q = 1) (hb : d124671 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92917, d124671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92917, d124671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92918 q = 1) (hb : d124672 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92918, d124672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92918, d124672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36578 (p : Pattern) (ha : d53030 p = 1) (hb : d124677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15155 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15155, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15155, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53030 q = 1) (hb : d124677 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53030, d124677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53030, d124677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36579 (p : Pattern) (ha : d53054 p = 1) (hb : d124691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53044 q = 1) (hb : d124682 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53044, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36578 q ha hb
    | true =>
      simp only [d53044, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28835 q hb ha
  have h2 (q : Pattern) (ha : d53045 q = 1) (hb : d124683 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53045, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53045, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53046 q = 1) (hb : d124684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53046, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53046, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53048 q = 1) (hb : d124685 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53048, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53048, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53053 q = 1) (hb : d124690 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53053, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53053, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53054 q = 1) (hb : d124691 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53054, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53054, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36580 (p : Pattern) (ha : d53064 p = 1) (hb : d124701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53062 q = 1) (hb : d124699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53062, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53062, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53063 q = 1) (hb : d124700 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53063, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53063, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53064 q = 1) (hb : d124701 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53064, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53064, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36581 (p : Pattern) (ha : d53074 p = 1) (hb : d124711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53062 q = 1) (hb : d124699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53062, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53062, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53063 q = 1) (hb : d124700 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53063, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53063, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53074 q = 1) (hb : d124711 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53074, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53074, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36582 (p : Pattern) (ha : d53164 p = 1) (hb : d124814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53153 q = 1) (hb : d124803 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53153, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36580 q ha hb
    | true =>
      simp only [d53153, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53154 q = 1) (hb : d124804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53154, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53154, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53155 q = 1) (hb : d124805 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53155, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53155, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53156 q = 1) (hb : d124806 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53156, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53156, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53157 q = 1) (hb : d124807 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53157, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53157, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53159 q = 1) (hb : d124809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53159, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36581 q ha hb
    | true =>
      simp only [d53159, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53160 q = 1) (hb : d124810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53160, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53160, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53161 q = 1) (hb : d124811 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53161, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53161, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53162 q = 1) (hb : d124812 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53162, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53162, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53163 q = 1) (hb : d124813 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53163, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53163, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53164 q = 1) (hb : d124814 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53164, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53164, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36583 (p : Pattern) (ha : d53173 p = 1) (hb : d124823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53159 q = 1) (hb : d124809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53159, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36581 q ha hb
    | true =>
      simp only [d53159, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53160 q = 1) (hb : d124810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53160, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53160, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53161 q = 1) (hb : d124811 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53161, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53161, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53162 q = 1) (hb : d124812 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53162, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53162, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53163 q = 1) (hb : d124813 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53163, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53163, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53173 q = 1) (hb : d124823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53173, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53173, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36584 (p : Pattern) (ha : d53204 p = 1) (hb : d124835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h2 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1863 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1864 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1865 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15407 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15407, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15407, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53204 q = 1) (hb : d124835 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53204, d124835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53204, d124835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36585 (p : Pattern) (ha : d53233 p = 1) (hb : d124861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53215 q = 1) (hb : d124856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53215, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36584 q ha hb
    | true =>
      simp only [d53215, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28841 q hb ha
  have h2 (q : Pattern) (ha : d53216 q = 1) (hb : d124857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53216, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53216, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53217 q = 1) (hb : d124858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53217, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53217, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53223 q = 1) (hb : d124859 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53223, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53223, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53232 q = 1) (hb : d124860 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53232, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53232, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53233 q = 1) (hb : d124861 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53233, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53233, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36586 (p : Pattern) (ha : d53244 p = 1) (hb : d124888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53234 q = 1) (hb : d124862 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53234, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36585 q ha hb
    | true =>
      simp only [d53234, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53235 q = 1) (hb : d124863 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53235, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53235, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53241 q = 1) (hb : d124885 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53241, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53241, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53242 q = 1) (hb : d124886 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53242, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53242, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53243 q = 1) (hb : d124887 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53243, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53243, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53244 q = 1) (hb : d124888 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53244, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53244, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36587 (p : Pattern) (ha : d53259 p = 1) (hb : d124894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53254 q = 1) (hb : d124889 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53254, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36586 q ha hb
    | true =>
      simp only [d53254, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53255 q = 1) (hb : d124890 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53255, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53255, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53256 q = 1) (hb : d124891 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53256, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53256, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53257 q = 1) (hb : d124892 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53257, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53257, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53258 q = 1) (hb : d124893 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53258, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53258, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53259 q = 1) (hb : d124894 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53259, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53259, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36588 (p : Pattern) (ha : d53028 p = 1) (hb : d124676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15150 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15150, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15150, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53028 q = 1) (hb : d124676 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53028, d124676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53028, d124676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36589 (p : Pattern) (ha : d92923 p = 1) (hb : d124687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53031 q = 1) (hb : d124678 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53031, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36588 q ha hb
    | true =>
      simp only [d53031, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36578 q ha hb
  have h2 (q : Pattern) (ha : d53032 q = 1) (hb : d124679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53032, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53032, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53033 q = 1) (hb : d124680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53033, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53033, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81822 q = 1) (hb : d124681 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81822, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81822, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53044 q = 1) (hb : d124682 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53044, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36578 q ha hb
    | true =>
      simp only [d53044, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28835 q hb ha
  have h6 (q : Pattern) (ha : d53045 q = 1) (hb : d124683 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53045, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53045, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53046 q = 1) (hb : d124684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53046, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53046, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53048 q = 1) (hb : d124685 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53048, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53048, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92922 q = 1) (hb : d124686 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92922, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92922, d124686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92923 q = 1) (hb : d124687 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92923, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92923, d124687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36590 (p : Pattern) (ha : d92929 p = 1) (hb : d124697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36589 q ha hb
    | true =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92927 q = 1) (hb : d124695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92927, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92927, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92928 q = 1) (hb : d124696 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92928, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92928, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92929 q = 1) (hb : d124697 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92929, d124697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92929, d124697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36591 (p : Pattern) (ha : d92935 p = 1) (hb : d124707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92930 q = 1) (hb : d124702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36590 q ha hb
    | true =>
      simp only [d92930, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36580 q ha hb
  have h2 (q : Pattern) (ha : d92931 q = 1) (hb : d124703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92931, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92931, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92932 q = 1) (hb : d124704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92932, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92932, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92933 q = 1) (hb : d124705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92933, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92933, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92934 q = 1) (hb : d124706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92934, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92934, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92935 q = 1) (hb : d124707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92935, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92935, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36592 (p : Pattern) (ha : d92938 p = 1) (hb : d124710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36589 q ha hb
    | true =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92927 q = 1) (hb : d124695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92927, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92927, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92928 q = 1) (hb : d124696 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92928, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92928, d124696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92938 q = 1) (hb : d124710 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92938, d124710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92938, d124710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36593 (p : Pattern) (ha : d92944 p = 1) (hb : d124717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92930 q = 1) (hb : d124702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36590 q ha hb
    | true =>
      simp only [d92930, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36580 q ha hb
  have h2 (q : Pattern) (ha : d92931 q = 1) (hb : d124703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92931, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92931, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92932 q = 1) (hb : d124704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92932, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92932, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92933 q = 1) (hb : d124705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92933, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92933, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92934 q = 1) (hb : d124706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92934, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92934, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92939 q = 1) (hb : d124712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92939, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36592 q ha hb
    | true =>
      simp only [d92939, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36581 q ha hb
  have h7 (q : Pattern) (ha : d92940 q = 1) (hb : d124713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92940, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92940, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92941 q = 1) (hb : d124714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92941, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92941, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92942 q = 1) (hb : d124715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92942, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92942, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92943 q = 1) (hb : d124716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92943, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92943, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92944 q = 1) (hb : d124717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92944, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92944, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36594 (p : Pattern) (ha : d53087 p = 1) (hb : d124724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53062 q = 1) (hb : d124699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53062, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53062, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53086 q = 1) (hb : d124723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53086, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53086, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53087 q = 1) (hb : d124724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53087, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53087, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36595 (p : Pattern) (ha : d53097 p = 1) (hb : d124734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53095 q = 1) (hb : d124732 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53095, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53095, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53096 q = 1) (hb : d124733 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53096, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53096, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53097 q = 1) (hb : d124734 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53097, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53097, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36596 (p : Pattern) (ha : d92949 p = 1) (hb : d124722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36589 q ha hb
    | true =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92927 q = 1) (hb : d124695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92927, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92927, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92948 q = 1) (hb : d124721 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92948, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92948, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92949 q = 1) (hb : d124722 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92949, d124722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92949, d124722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36597 (p : Pattern) (ha : d92956 p = 1) (hb : d124731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36589 q ha hb
    | true =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92954 q = 1) (hb : d124729 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92954, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92954, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92955 q = 1) (hb : d124730 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92955, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92955, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92956 q = 1) (hb : d124731 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92956, d124731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92956, d124731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36598 (p : Pattern) (ha : d81824 p = 1) (hb : d124752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53031 q = 1) (hb : d124678 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53031, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36588 q ha hb
    | true =>
      simp only [d53031, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36578 q ha hb
  have h2 (q : Pattern) (ha : d53032 q = 1) (hb : d124679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53032, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53032, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53033 q = 1) (hb : d124680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53033, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53033, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81822 q = 1) (hb : d124681 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81822, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81822, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69227 q = 1) (hb : d124747 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69227, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34933 q ha hb
    | true =>
      simp only [d69227, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7965 q hb ha
  have h6 (q : Pattern) (ha : d69228 q = 1) (hb : d124748 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69228, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69228, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69229 q = 1) (hb : d124749 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69229, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69229, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69230 q = 1) (hb : d124750 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69230, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69230, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d81823 q = 1) (hb : d124751 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81823, d124751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81823, d124751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81824 q = 1) (hb : d124752 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81824, d124752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81824, d124752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36599 (p : Pattern) (ha : d53111 p = 1) (hb : d124738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1667 q = 1) (hb : d53108 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1667, d53108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1668 q = 1) (hb : d53109 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1668, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1668, d53109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15228 q = 1) (hb : d53110 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15228, d53110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15228, d53110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53111 q = 1) (hb : d124738 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53111, d124738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53111, d124738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36600 (p : Pattern) (ha : d92962 p = 1) (hb : d124744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53112 q = 1) (hb : d124739 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53112, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36599 q ha hb
    | true =>
      simp only [d53112, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36588 q ha hb
  have h2 (q : Pattern) (ha : d53113 q = 1) (hb : d124740 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53113, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53113, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53114 q = 1) (hb : d124741 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53114, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53114, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92960 q = 1) (hb : d124742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d92960, d124742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92960, d124742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53031 q = 1) (hb : d124678 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53031, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36588 q ha hb
    | true =>
      simp only [d53031, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36578 q ha hb
  have h6 (q : Pattern) (ha : d53032 q = 1) (hb : d124679 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53032, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53032, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53033 q = 1) (hb : d124680 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53033, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53033, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81822 q = 1) (hb : d124681 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81822, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81822, d124681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92961 q = 1) (hb : d124743 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92961, d124743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92961, d124743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92962 q = 1) (hb : d124744 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92962, d124744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92962, d124744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36601 (p : Pattern) (ha : d92968 p = 1) (hb : d124758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92963 q = 1) (hb : d124745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92963, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36600 q ha hb
    | true =>
      simp only [d92963, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92964 q = 1) (hb : d124746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92964, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92964, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81825 q = 1) (hb : d124753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81825, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36598 q ha hb
    | true =>
      simp only [d81825, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81826 q = 1) (hb : d124754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81826, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81826, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92965 q = 1) (hb : d124755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92965, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92965, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92966 q = 1) (hb : d124756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92966, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92966, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92967 q = 1) (hb : d124757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92967, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92967, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92968 q = 1) (hb : d124758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92968, d124758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92968, d124758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36602 (p : Pattern) (ha : d92972 p = 1) (hb : d124762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81825 q = 1) (hb : d124753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81825, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36598 q ha hb
    | true =>
      simp only [d81825, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81826 q = 1) (hb : d124754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81826, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81826, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92969 q = 1) (hb : d124759 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92969, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92969, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92970 q = 1) (hb : d124760 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92970, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92970, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92971 q = 1) (hb : d124761 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92971, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92971, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92972 q = 1) (hb : d124762 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92972, d124762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92972, d124762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36603 (p : Pattern) (ha : d92978 p = 1) (hb : d124768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36589 q ha hb
    | true =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92975 q = 1) (hb : d124765 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92975, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92975, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92976 q = 1) (hb : d124766 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92976, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92976, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92977 q = 1) (hb : d124767 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92977, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92977, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92978 q = 1) (hb : d124768 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92978, d124768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92978, d124768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36604 (p : Pattern) (ha : d92984 p = 1) (hb : d124774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92950 q = 1) (hb : d124725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92950, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36596 q ha hb
    | true =>
      simp only [d92950, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36594 q ha hb
  have h2 (q : Pattern) (ha : d92951 q = 1) (hb : d124726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92951, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92951, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92952 q = 1) (hb : d124727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92952, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92952, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92953 q = 1) (hb : d124728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92953, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92953, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92957 q = 1) (hb : d124735 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92957, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36597 q ha hb
    | true =>
      simp only [d92957, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36595 q ha hb
  have h6 (q : Pattern) (ha : d92958 q = 1) (hb : d124736 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92958, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92958, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92959 q = 1) (hb : d124737 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92959, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92959, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92973 q = 1) (hb : d124763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92973, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36601 q ha hb
    | true =>
      simp only [d92973, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36602 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92930 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92974 q = 1) (hb : d124764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92974, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92979 q = 1) (hb : d124769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92979, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36603 q ha hb
    | true =>
      simp only [d92979, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92980 q = 1) (hb : d124770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92980, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92980, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92981 q = 1) (hb : d124771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92981, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92982 q = 1) (hb : d124772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92982, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92983 q = 1) (hb : d124773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92983, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92984 q = 1) (hb : d124774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92984, d124774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92984, d124774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro36605 (p : Pattern) (ha : d53133 p = 1) (hb : d124776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53062 q = 1) (hb : d124699 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53062, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53062, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53086 q = 1) (hb : d124723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53086, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53086, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53133 q = 1) (hb : d124776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53133, d124776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53133, d124776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36606 (p : Pattern) (ha : d53139 p = 1) (hb : d124782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53061 q = 1) (hb : d124698 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53061, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53095 q = 1) (hb : d124732 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53095, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53095, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53096 q = 1) (hb : d124733 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53096, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53096, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53139 q = 1) (hb : d124782 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53139, d124782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53139, d124782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36607 (p : Pattern) (ha : d92985 p = 1) (hb : d124775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36589 q ha hb
    | true =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92927 q = 1) (hb : d124695 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92927, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92927, d124695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92948 q = 1) (hb : d124721 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92948, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92948, d124721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92985 q = 1) (hb : d124775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92985, d124775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92985, d124775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36608 (p : Pattern) (ha : d92990 p = 1) (hb : d124781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36589 q ha hb
    | true =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92926 q = 1) (hb : d124694 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92926, d124694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92954 q = 1) (hb : d124729 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92954, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92954, d124729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92955 q = 1) (hb : d124730 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92955, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92955, d124730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92990 q = 1) (hb : d124781 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92990, d124781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92990, d124781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36609 (p : Pattern) (ha : d92994 p = 1) (hb : d124786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92963 q = 1) (hb : d124745 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92963, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36600 q ha hb
    | true =>
      simp only [d92963, d124745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92964 q = 1) (hb : d124746 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92964, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92964, d124746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81825 q = 1) (hb : d124753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81825, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36598 q ha hb
    | true =>
      simp only [d81825, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81826 q = 1) (hb : d124754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81826, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81826, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92965 q = 1) (hb : d124755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92965, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92965, d124755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92966 q = 1) (hb : d124756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92966, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92966, d124756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92967 q = 1) (hb : d124757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92967, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92967, d124757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92994 q = 1) (hb : d124786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92994, d124786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92994, d124786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36610 (p : Pattern) (ha : d92995 p = 1) (hb : d124787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81825 q = 1) (hb : d124753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81825, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36598 q ha hb
    | true =>
      simp only [d81825, d124753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81826 q = 1) (hb : d124754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81826, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81826, d124754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53055 q = 1) (hb : d124692 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36579 q ha hb
    | true =>
      simp only [d53055, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d124693 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53056, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92969 q = 1) (hb : d124759 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92969, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92969, d124759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92970 q = 1) (hb : d124760 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92970, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92970, d124760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92971 q = 1) (hb : d124761 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92971, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92971, d124761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92995 q = 1) (hb : d124787 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92995, d124787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92995, d124787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36611 (p : Pattern) (ha : d92998 p = 1) (hb : d124790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92924 q = 1) (hb : d124688 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36589 q ha hb
    | true =>
      simp only [d92924, d124688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92925 q = 1) (hb : d124689 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92925, d124689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92975 q = 1) (hb : d124765 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92975, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92975, d124765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92976 q = 1) (hb : d124766 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92976, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92976, d124766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92977 q = 1) (hb : d124767 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92977, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92977, d124767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92998 q = 1) (hb : d124790 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92998, d124790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92998, d124790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36612 (p : Pattern) (ha : d93004 p = 1) (hb : d124796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92950 q = 1) (hb : d124725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92950, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36596 q ha hb
    | true =>
      simp only [d92950, d124725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36594 q ha hb
  have h2 (q : Pattern) (ha : d92951 q = 1) (hb : d124726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92951, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92951, d124726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92952 q = 1) (hb : d124727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92952, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92952, d124727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92953 q = 1) (hb : d124728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92953, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92953, d124728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92957 q = 1) (hb : d124735 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92957, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36597 q ha hb
    | true =>
      simp only [d92957, d124735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36595 q ha hb
  have h6 (q : Pattern) (ha : d92958 q = 1) (hb : d124736 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92958, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92958, d124736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92959 q = 1) (hb : d124737 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92959, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92959, d124737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92973 q = 1) (hb : d124763 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92973, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36601 q ha hb
    | true =>
      simp only [d92973, d124763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36602 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92930 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92974 q = 1) (hb : d124764 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92974, d124764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92979 q = 1) (hb : d124769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92979, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36603 q ha hb
    | true =>
      simp only [d92979, d124769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92980 q = 1) (hb : d124770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92980, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92980, d124770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92981 q = 1) (hb : d124771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92981, d124771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92982 q = 1) (hb : d124772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92982, d124772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92983 q = 1) (hb : d124773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92983, d124773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92986 q = 1) (hb : d124777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92986, d124777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36607 q ha hb
    | true =>
      simp only [d92986, d124777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36605 q ha hb
  have h17 (q : Pattern) (ha : d92987 q = 1) (hb : d124778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92987, d124778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92987, d124778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92988 q = 1) (hb : d124779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92988, d124779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92988, d124779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92989 q = 1) (hb : d124780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92989, d124780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92989, d124780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92991 q = 1) (hb : d124783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92991, d124783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36608 q ha hb
    | true =>
      simp only [d92991, d124783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36606 q ha hb
  have h21 (q : Pattern) (ha : d92992 q = 1) (hb : d124784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92992, d124784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92992, d124784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92993 q = 1) (hb : d124785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92993, d124785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92993, d124785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92996 q = 1) (hb : d124788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92996, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36609 q ha hb
    | true =>
      simp only [d92996, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36610 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92939 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92997 q = 1) (hb : d124789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92997, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92999 q = 1) (hb : d124791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92999, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36611 q ha hb
    | true =>
      simp only [d92999, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d93000 q = 1) (hb : d124792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93000, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d93000, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d93001 q = 1) (hb : d124793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d93001, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d93002 q = 1) (hb : d124794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93002, d124794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d93002, d124794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d93003 q = 1) (hb : d124795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93003, d124795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93003, d124795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d93004 q = 1) (hb : d124796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93004, d124796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93004, d124796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro36613 (p : Pattern) (ha : d93011 p = 1) (hb : d124808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93006 q = 1) (hb : d124798 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93006, d124798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36602 q ha hb
    | true =>
      simp only [d93006, d124798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36580 q ha hb
  have h2 (q : Pattern) (ha : d93007 q = 1) (hb : d124799 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93007, d124799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93007, d124799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93008 q = 1) (hb : d124800 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93008, d124800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93008, d124800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93009 q = 1) (hb : d124801 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93009, d124801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93009, d124801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93010 q = 1) (hb : d124802 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93010, d124802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93010, d124802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53153 q = 1) (hb : d124803 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53153, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36580 q ha hb
    | true =>
      simp only [d53153, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53154 q = 1) (hb : d124804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53154, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53154, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53155 q = 1) (hb : d124805 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53155, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53155, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53156 q = 1) (hb : d124806 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53156, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53156, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53157 q = 1) (hb : d124807 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53157, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53157, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93011 q = 1) (hb : d124808 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93011, d124808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93011, d124808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36614 (p : Pattern) (ha : d93018 p = 1) (hb : d124821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92996 q = 1) (hb : d124788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92996, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36609 q ha hb
    | true =>
      simp only [d92996, d124788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36610 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92939 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92997 q = 1) (hb : d124789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92997, d124789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92999 q = 1) (hb : d124791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92999, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36611 q ha hb
    | true =>
      simp only [d92999, d124791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93000 q = 1) (hb : d124792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93000, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93000, d124792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93001 q = 1) (hb : d124793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93001, d124793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93016 q = 1) (hb : d124819 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93016, d124819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93016, d124819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93017 q = 1) (hb : d124820 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93017, d124820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93017, d124820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93018 q = 1) (hb : d124821 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93018, d124821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93018, d124821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36615 (p : Pattern) (ha : d53199 p = 1) (hb : d124830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1857 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
  have h2 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1858 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1858, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1859 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1859, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1860 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1860, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15386 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15386, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15386, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53199 q = 1) (hb : d124830 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53199, d124830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53199, d124830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36616 (p : Pattern) (ha : d81870 p = 1) (hb : d124849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53205 q = 1) (hb : d124836 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53205, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36615 q ha hb
    | true =>
      simp only [d53205, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36584 q ha hb
  have h2 (q : Pattern) (ha : d53206 q = 1) (hb : d124837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53206, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53206, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53207 q = 1) (hb : d124838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53207, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53207, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81868 q = 1) (hb : d124839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81868, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81868, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76231 q = 1) (hb : d124844 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34967 q ha hb
    | true =>
      simp only [d76231, d124844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10901 q hb ha
  have h6 (q : Pattern) (ha : d76232 q = 1) (hb : d124845 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d124845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76233 q = 1) (hb : d124846 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d124846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76234 q = 1) (hb : d124847 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76234, d124847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76234, d124847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d81869 q = 1) (hb : d124848 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81869, d124848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81869, d124848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81870 q = 1) (hb : d124849 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81870, d124849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81870, d124849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36617 (p : Pattern) (ha : d53193 p = 1) (hb : d124829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1853 q = 1) (hb : d53179 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d53179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
  have h2 (q : Pattern) (ha : d1665 q = 1) (hb : d53106 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro230 q ha hb
    | true =>
      simp only [d1665, d53106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1854 q = 1) (hb : d53180 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1854, d53180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1666 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1666, d53107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1855 q = 1) (hb : d53181 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1855, d53181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1856 q = 1) (hb : d53182 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1856, d53182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15379 q = 1) (hb : d53187 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15379, d53187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15379, d53187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53193 q = 1) (hb : d124829 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53193, d124829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53193, d124829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36618 (p : Pattern) (ha : d93026 p = 1) (hb : d124841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53200 q = 1) (hb : d124831 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53200, d124831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36617 q ha hb
    | true =>
      simp only [d53200, d124831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36615 q ha hb
  have h2 (q : Pattern) (ha : d53201 q = 1) (hb : d124832 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53201, d124832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53201, d124832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53202 q = 1) (hb : d124833 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53202, d124833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53202, d124833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93024 q = 1) (hb : d124834 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d93024, d124834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93024, d124834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53205 q = 1) (hb : d124836 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53205, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36615 q ha hb
    | true =>
      simp only [d53205, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36584 q ha hb
  have h6 (q : Pattern) (ha : d53206 q = 1) (hb : d124837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53206, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53206, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53207 q = 1) (hb : d124838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53207, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53207, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81868 q = 1) (hb : d124839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81868, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81868, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d93025 q = 1) (hb : d124840 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93025, d124840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93025, d124840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93026 q = 1) (hb : d124841 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93026, d124841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93026, d124841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36619 (p : Pattern) (ha : d93032 p = 1) (hb : d124855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93027 q = 1) (hb : d124842 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93027, d124842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36618 q ha hb
    | true =>
      simp only [d93027, d124842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93028 q = 1) (hb : d124843 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93028, d124843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93028, d124843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81871 q = 1) (hb : d124850 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81871, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36616 q ha hb
    | true =>
      simp only [d81871, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81872 q = 1) (hb : d124851 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81872, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81872, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93029 q = 1) (hb : d124852 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93029, d124852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93029, d124852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93030 q = 1) (hb : d124853 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93030, d124853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93030, d124853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93031 q = 1) (hb : d124854 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93031, d124854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93031, d124854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93032 q = 1) (hb : d124855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93032, d124855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93032, d124855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36620 (p : Pattern) (ha : d93036 p = 1) (hb : d124867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81871 q = 1) (hb : d124850 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81871, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36616 q ha hb
    | true =>
      simp only [d81871, d124850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81872 q = 1) (hb : d124851 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81872, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81872, d124851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53234 q = 1) (hb : d124862 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53234, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36585 q ha hb
    | true =>
      simp only [d53234, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53235 q = 1) (hb : d124863 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53235, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53235, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93033 q = 1) (hb : d124864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93033, d124864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93033, d124864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93034 q = 1) (hb : d124865 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93034, d124865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93034, d124865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93035 q = 1) (hb : d124866 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93035, d124866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93035, d124866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93036 q = 1) (hb : d124867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93036, d124867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93036, d124867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36621 (p : Pattern) (ha : d93039 p = 1) (hb : d124871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53205 q = 1) (hb : d124836 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53205, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36615 q ha hb
    | true =>
      simp only [d53205, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36584 q ha hb
  have h2 (q : Pattern) (ha : d53206 q = 1) (hb : d124837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53206, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53206, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53207 q = 1) (hb : d124838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53207, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53207, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81868 q = 1) (hb : d124839 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81868, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81868, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53215 q = 1) (hb : d124856 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53215, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36584 q ha hb
    | true =>
      simp only [d53215, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28841 q hb ha
  have h6 (q : Pattern) (ha : d53216 q = 1) (hb : d124857 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53216, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53216, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53217 q = 1) (hb : d124858 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53217, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53217, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53223 q = 1) (hb : d124859 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53223, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53223, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d93038 q = 1) (hb : d124870 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93038, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93038, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93039 q = 1) (hb : d124871 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93039, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93039, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36622 (p : Pattern) (ha : d93051 p = 1) (hb : d124877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93040 q = 1) (hb : d124872 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93040, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36621 q ha hb
    | true =>
      simp only [d93040, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93041 q = 1) (hb : d124873 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93041, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93041, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93048 q = 1) (hb : d124874 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93048, d124874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93048, d124874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93049 q = 1) (hb : d124875 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93049, d124875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93049, d124875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93050 q = 1) (hb : d124876 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93050, d124876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93050, d124876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93051 q = 1) (hb : d124877 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93051, d124877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93051, d124877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36623 (p : Pattern) (ha : d93057 p = 1) (hb : d124883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93037 q = 1) (hb : d124868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93037, d124868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36619 q ha hb
    | true =>
      simp only [d93037, d124868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36620 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93046 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93047 q = 1) (hb : d124869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93047, d124869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93047, d124869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d93052 q = 1) (hb : d124878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93052, d124878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36622 q ha hb
    | true =>
      simp only [d93052, d124878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93053 q = 1) (hb : d124879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93053, d124879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93053, d124879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93054 q = 1) (hb : d124880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93054, d124880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93054, d124880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93055 q = 1) (hb : d124881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93055, d124881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93055, d124881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93056 q = 1) (hb : d124882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93056, d124882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93056, d124882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93057 q = 1) (hb : d124883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93057, d124883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93057, d124883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36624 (p : Pattern) (ha : d93063 p = 1) (hb : d124900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92936 q = 1) (hb : d124708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92936, d124708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92936, d124708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36591 q ha hb
  have h2 (q : Pattern) (ha : d92937 q = 1) (hb : d124709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92937, d124709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92937, d124709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92945 q = 1) (hb : d124718 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92945, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36591 q ha hb
    | true =>
      simp only [d92945, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36593 q ha hb
  have h4 (q : Pattern) (ha : d92946 q = 1) (hb : d124719 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92946, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92946, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92947 q = 1) (hb : d124720 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92947, d124720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92947, d124720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93005 q = 1) (hb : d124797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93005, d124797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36604 q ha hb
    | true =>
      simp only [d93005, d124797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36612 q ha hb
  have h7 (q : Pattern) (ha : d93012 q = 1) (hb : d124815 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93012, d124815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36613 q ha hb
    | true =>
      simp only [d93012, d124815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36582 q ha hb
  have h8 (q : Pattern) (ha : d93013 q = 1) (hb : d124816 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93013, d124816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93013, d124816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93014 q = 1) (hb : d124817 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93014, d124817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93014, d124817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d93015 q = 1) (hb : d124818 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93015, d124818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93015, d124818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93019 q = 1) (hb : d124822 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93019, d124822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93019, d124822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36614 q ha hb
  have h12 (q : Pattern) (ha : d53174 q = 1) (hb : d124824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53174, d124824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53174, d124824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36583 q ha hb
  have h13 (q : Pattern) (ha : d93020 q = 1) (hb : d124825 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93020, d124825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93020, d124825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93021 q = 1) (hb : d124826 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93021, d124826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93021, d124826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d93022 q = 1) (hb : d124827 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93022, d124827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d93022, d124827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d93023 q = 1) (hb : d124828 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93023, d124828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93023, d124828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93058 q = 1) (hb : d124884 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93058, d124884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93058, d124884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36623 q ha hb
  have h18 (q : Pattern) (ha : d53260 q = 1) (hb : d124895 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53260, d124895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53260, d124895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36587 q ha hb
  have h19 (q : Pattern) (ha : d93059 q = 1) (hb : d124896 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93059, d124896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93059, d124896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d93060 q = 1) (hb : d124897 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93060, d124897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93060, d124897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d93061 q = 1) (hb : d124898 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93061, d124898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d93061, d124898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d93062 q = 1) (hb : d124899 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93062, d124899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d93062, d124899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d93063 q = 1) (hb : d124900 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93063, d124900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93063, d124900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36625 (p : Pattern) (ha : d93069 p = 1) (hb : d124906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93064 q = 1) (hb : d124901 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93064, d124901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93064, d124901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36624 q ha hb
  have h2 (q : Pattern) (ha : d93065 q = 1) (hb : d124902 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93065, d124902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93065, d124902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93066 q = 1) (hb : d124903 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93066, d124903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93066, d124903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93067 q = 1) (hb : d124904 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93067, d124904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93067, d124904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93068 q = 1) (hb : d124905 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93068, d124905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93068, d124905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93069 q = 1) (hb : d124906 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93069, d124906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93069, d124906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36626 (p : Pattern) (ha : d53351 p = 1) (hb : d124912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2055 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2056 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15547 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15547, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15547, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53351 q = 1) (hb : d124912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53351, d124912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53351, d124912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36627 (p : Pattern) (ha : d53375 p = 1) (hb : d124926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53365 q = 1) (hb : d124917 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53365, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36626 q ha hb
    | true =>
      simp only [d53365, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28881 q hb ha
  have h2 (q : Pattern) (ha : d53366 q = 1) (hb : d124918 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53366, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53366, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53367 q = 1) (hb : d124919 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53367, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53367, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53369 q = 1) (hb : d124920 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53369, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53369, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53374 q = 1) (hb : d124925 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53374, d124925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53374, d124925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53375 q = 1) (hb : d124926 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53375, d124926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53375, d124926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36628 (p : Pattern) (ha : d53385 p = 1) (hb : d124936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53383 q = 1) (hb : d124934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53383, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53383, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53384 q = 1) (hb : d124935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53384, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53384, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53385 q = 1) (hb : d124936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53385, d124936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53385, d124936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36629 (p : Pattern) (ha : d53395 p = 1) (hb : d124946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53383 q = 1) (hb : d124934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53383, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53383, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53384 q = 1) (hb : d124935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53384, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53384, d124935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53395 q = 1) (hb : d124946 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53395, d124946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53395, d124946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36630 (p : Pattern) (ha : d53481 p = 1) (hb : d125048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53470 q = 1) (hb : d125037 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53470, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36628 q ha hb
    | true =>
      simp only [d53470, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53471 q = 1) (hb : d125038 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53471, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53471, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53472 q = 1) (hb : d125039 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53472, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53472, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53473 q = 1) (hb : d125040 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53473, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53473, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53474 q = 1) (hb : d125041 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53474, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53474, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53476 q = 1) (hb : d125043 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53476, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36629 q ha hb
    | true =>
      simp only [d53476, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53477 q = 1) (hb : d125044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53477, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53477, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53478 q = 1) (hb : d125045 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53478, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53478, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53479 q = 1) (hb : d125046 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53479, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53479, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53480 q = 1) (hb : d125047 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53480, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53480, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53481 q = 1) (hb : d125048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53481, d125048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53481, d125048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36631 (p : Pattern) (ha : d53490 p = 1) (hb : d125057 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53476 q = 1) (hb : d125043 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53476, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36629 q ha hb
    | true =>
      simp only [d53476, d125043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53477 q = 1) (hb : d125044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53477, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53477, d125044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53478 q = 1) (hb : d125045 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53478, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53478, d125045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53479 q = 1) (hb : d125046 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53479, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53479, d125046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53480 q = 1) (hb : d125047 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53480, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53480, d125047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53490 q = 1) (hb : d125057 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53490, d125057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53490, d125057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36632 (p : Pattern) (ha : d53521 p = 1) (hb : d125068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2340 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
  have h2 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2341 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2342 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2343 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15785 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15785, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15785, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53521 q = 1) (hb : d125068 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53521, d125068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53521, d125068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36633 (p : Pattern) (ha : d53550 p = 1) (hb : d125094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53532 q = 1) (hb : d125089 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53532, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36632 q ha hb
    | true =>
      simp only [d53532, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28887 q hb ha
  have h2 (q : Pattern) (ha : d53533 q = 1) (hb : d125090 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53533, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53533, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53534 q = 1) (hb : d125091 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53534, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53534, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53540 q = 1) (hb : d125092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53540, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53540, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53549 q = 1) (hb : d125093 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d53549, d125093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53549, d125093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53550 q = 1) (hb : d125094 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d53550, d125094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53550, d125094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36634 (p : Pattern) (ha : d53561 p = 1) (hb : d125121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53551 q = 1) (hb : d125095 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53551, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36633 q ha hb
    | true =>
      simp only [d53551, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53552 q = 1) (hb : d125096 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53552, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53552, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53558 q = 1) (hb : d125118 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53558, d125118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53558, d125118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53559 q = 1) (hb : d125119 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53559, d125119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53559, d125119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53560 q = 1) (hb : d125120 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53560, d125120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53560, d125120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53561 q = 1) (hb : d125121 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53561, d125121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53561, d125121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36635 (p : Pattern) (ha : d53576 p = 1) (hb : d125127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53571 q = 1) (hb : d125122 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53571, d125122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36634 q ha hb
    | true =>
      simp only [d53571, d125122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53572 q = 1) (hb : d125123 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53572, d125123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53572, d125123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53573 q = 1) (hb : d125124 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53573, d125124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53573, d125124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53574 q = 1) (hb : d125125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53574, d125125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53574, d125125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53575 q = 1) (hb : d125126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53575, d125126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53575, d125126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53576 q = 1) (hb : d125127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53576, d125127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53576, d125127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36636 (p : Pattern) (ha : d53349 p = 1) (hb : d124911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2037 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2037, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2038 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15544 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15544, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15544, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53349 q = 1) (hb : d124911 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53349, d124911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53349, d124911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro36637 (p : Pattern) (ha : d93075 p = 1) (hb : d124922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53352 q = 1) (hb : d124913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53352, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36636 q ha hb
    | true =>
      simp only [d53352, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36626 q ha hb
  have h2 (q : Pattern) (ha : d53353 q = 1) (hb : d124914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53353, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53353, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53354 q = 1) (hb : d124915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53354, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53354, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81903 q = 1) (hb : d124916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81903, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81903, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53365 q = 1) (hb : d124917 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53365, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36626 q ha hb
    | true =>
      simp only [d53365, d124917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28881 q hb ha
  have h6 (q : Pattern) (ha : d53366 q = 1) (hb : d124918 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53366, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53366, d124918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53367 q = 1) (hb : d124919 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53367, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53367, d124919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53369 q = 1) (hb : d124920 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53369, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53369, d124920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d93074 q = 1) (hb : d124921 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93074, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93074, d124921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93075 q = 1) (hb : d124922 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93075, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93075, d124922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36638 (p : Pattern) (ha : d93081 p = 1) (hb : d124932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36637 q ha hb
    | true =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93079 q = 1) (hb : d124930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93079, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93079, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93080 q = 1) (hb : d124931 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93080, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93080, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93081 q = 1) (hb : d124932 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93081, d124932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93081, d124932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36639 (p : Pattern) (ha : d93087 p = 1) (hb : d124942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93082 q = 1) (hb : d124937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36638 q ha hb
    | true =>
      simp only [d93082, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36628 q ha hb
  have h2 (q : Pattern) (ha : d93083 q = 1) (hb : d124938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93083, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93083, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93084 q = 1) (hb : d124939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93084, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93084, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93085 q = 1) (hb : d124940 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93085, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93085, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93086 q = 1) (hb : d124941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93086, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93086, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93087 q = 1) (hb : d124942 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93087, d124942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93087, d124942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36640 (p : Pattern) (ha : d93090 p = 1) (hb : d124945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36637 q ha hb
    | true =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93079 q = 1) (hb : d124930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93079, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93079, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93080 q = 1) (hb : d124931 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93080, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93080, d124931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93090 q = 1) (hb : d124945 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93090, d124945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93090, d124945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36641 (p : Pattern) (ha : d93096 p = 1) (hb : d124952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93082 q = 1) (hb : d124937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93082, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36638 q ha hb
    | true =>
      simp only [d93082, d124937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36628 q ha hb
  have h2 (q : Pattern) (ha : d93083 q = 1) (hb : d124938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93083, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93083, d124938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93084 q = 1) (hb : d124939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93084, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93084, d124939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93085 q = 1) (hb : d124940 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93085, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93085, d124940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93086 q = 1) (hb : d124941 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93086, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93086, d124941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93091 q = 1) (hb : d124947 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93091, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36640 q ha hb
    | true =>
      simp only [d93091, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36629 q ha hb
  have h7 (q : Pattern) (ha : d93092 q = 1) (hb : d124948 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93092, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93092, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93093 q = 1) (hb : d124949 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93093, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93093, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d93094 q = 1) (hb : d124950 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93094, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93094, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93095 q = 1) (hb : d124951 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93095, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93095, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93096 q = 1) (hb : d124952 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93096, d124952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93096, d124952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36642 (p : Pattern) (ha : d53408 p = 1) (hb : d124959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53383 q = 1) (hb : d124934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53383, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53383, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53407 q = 1) (hb : d124958 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53407, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53407, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53408 q = 1) (hb : d124959 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53408, d124959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53408, d124959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36643 (p : Pattern) (ha : d53418 p = 1) (hb : d124969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53416 q = 1) (hb : d124967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53416, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53416, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53417 q = 1) (hb : d124968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53417, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53417, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53418 q = 1) (hb : d124969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53418, d124969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53418, d124969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36644 (p : Pattern) (ha : d93101 p = 1) (hb : d124957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36637 q ha hb
    | true =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93079 q = 1) (hb : d124930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93079, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93079, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93100 q = 1) (hb : d124956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93100, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93100, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93101 q = 1) (hb : d124957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93101, d124957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93101, d124957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36645 (p : Pattern) (ha : d93108 p = 1) (hb : d124966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36637 q ha hb
    | true =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93106 q = 1) (hb : d124964 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93106, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93106, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93107 q = 1) (hb : d124965 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93107, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93107, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93108 q = 1) (hb : d124966 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93108, d124966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93108, d124966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36646 (p : Pattern) (ha : d81905 p = 1) (hb : d124986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53352 q = 1) (hb : d124913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53352, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36636 q ha hb
    | true =>
      simp only [d53352, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36626 q ha hb
  have h2 (q : Pattern) (ha : d53353 q = 1) (hb : d124914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53353, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53353, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53354 q = 1) (hb : d124915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53354, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53354, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81903 q = 1) (hb : d124916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81903, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81903, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d69337 q = 1) (hb : d124981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34983 q ha hb
    | true =>
      simp only [d69337, d124981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7981 q hb ha
  have h6 (q : Pattern) (ha : d69338 q = 1) (hb : d124982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d124982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69339 q = 1) (hb : d124983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d124983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69340 q = 1) (hb : d124984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69340, d124984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d69340, d124984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d81904 q = 1) (hb : d124985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81904, d124985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81904, d124985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81905 q = 1) (hb : d124986 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81905, d124986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81905, d124986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36647 (p : Pattern) (ha : d15621 p = 1) (hb : d53428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2146 q = 1) (hb : d53425 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2146, d53425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2147 q = 1) (hb : d53426 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2147, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2147, d53426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15620 q = 1) (hb : d53427 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15620, d53427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15620, d53427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15621 q = 1) (hb : d53428 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15621, d53428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15621, d53428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36648 (p : Pattern) (ha : d93114 p = 1) (hb : d124978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53429 q = 1) (hb : d124973 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53429, d124973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36647 q hb ha
    | true =>
      simp only [d53429, d124973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36636 q ha hb
  have h2 (q : Pattern) (ha : d53430 q = 1) (hb : d124974 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53430, d124974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53430, d124974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53431 q = 1) (hb : d124975 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53431, d124975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53431, d124975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93112 q = 1) (hb : d124976 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d93112, d124976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93112, d124976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53352 q = 1) (hb : d124913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53352, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36636 q ha hb
    | true =>
      simp only [d53352, d124913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36626 q ha hb
  have h6 (q : Pattern) (ha : d53353 q = 1) (hb : d124914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53353, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53353, d124914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53354 q = 1) (hb : d124915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53354, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53354, d124915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81903 q = 1) (hb : d124916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81903, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81903, d124916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d93113 q = 1) (hb : d124977 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93113, d124977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93113, d124977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93114 q = 1) (hb : d124978 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93114, d124978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93114, d124978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36649 (p : Pattern) (ha : d93120 p = 1) (hb : d124992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93115 q = 1) (hb : d124979 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93115, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36648 q ha hb
    | true =>
      simp only [d93115, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93116 q = 1) (hb : d124980 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93116, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93116, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81906 q = 1) (hb : d124987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81906, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36646 q ha hb
    | true =>
      simp only [d81906, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81907 q = 1) (hb : d124988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81907, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81907, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93117 q = 1) (hb : d124989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93117, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93117, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93118 q = 1) (hb : d124990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93118, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93118, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93119 q = 1) (hb : d124991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93119, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93119, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93120 q = 1) (hb : d124992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93120, d124992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93120, d124992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36650 (p : Pattern) (ha : d93124 p = 1) (hb : d124996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81906 q = 1) (hb : d124987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81906, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36646 q ha hb
    | true =>
      simp only [d81906, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81907 q = 1) (hb : d124988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81907, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81907, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93121 q = 1) (hb : d124993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93121, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93121, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93122 q = 1) (hb : d124994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93122, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93122, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93123 q = 1) (hb : d124995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93123, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93123, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93124 q = 1) (hb : d124996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93124, d124996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93124, d124996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36651 (p : Pattern) (ha : d93130 p = 1) (hb : d125002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36637 q ha hb
    | true =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93127 q = 1) (hb : d124999 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93127, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93127, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93128 q = 1) (hb : d125000 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93128, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93128, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93129 q = 1) (hb : d125001 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93129, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93129, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93130 q = 1) (hb : d125002 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93130, d125002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93130, d125002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36652 (p : Pattern) (ha : d93136 p = 1) (hb : d125008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93102 q = 1) (hb : d124960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93102, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36644 q ha hb
    | true =>
      simp only [d93102, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36642 q ha hb
  have h2 (q : Pattern) (ha : d93103 q = 1) (hb : d124961 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93103, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93103, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93104 q = 1) (hb : d124962 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93104, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93104, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93105 q = 1) (hb : d124963 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93105, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93105, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93109 q = 1) (hb : d124970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93109, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36645 q ha hb
    | true =>
      simp only [d93109, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36643 q ha hb
  have h6 (q : Pattern) (ha : d93110 q = 1) (hb : d124971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93110, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93110, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93111 q = 1) (hb : d124972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93111, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93111, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93125 q = 1) (hb : d124997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93125, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36649 q ha hb
    | true =>
      simp only [d93125, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36650 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d93082 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d93126 q = 1) (hb : d124998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93126, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d93131 q = 1) (hb : d125003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93131, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36651 q ha hb
    | true =>
      simp only [d93131, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d93132 q = 1) (hb : d125004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93132, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93132, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d93133 q = 1) (hb : d125005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93133, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93134 q = 1) (hb : d125006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93134, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93135 q = 1) (hb : d125007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93135, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93136 q = 1) (hb : d125008 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93136, d125008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93136, d125008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro36653 (p : Pattern) (ha : d53450 p = 1) (hb : d125010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53383 q = 1) (hb : d124934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53383, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53383, d124934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53407 q = 1) (hb : d124958 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53407, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53407, d124958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53450 q = 1) (hb : d125010 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53450, d125010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53450, d125010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36654 (p : Pattern) (ha : d53456 p = 1) (hb : d125016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53382 q = 1) (hb : d124933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53382, d124933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53416 q = 1) (hb : d124967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53416, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53416, d124967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53417 q = 1) (hb : d124968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53417, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53417, d124968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53456 q = 1) (hb : d125016 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53456, d125016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53456, d125016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36655 (p : Pattern) (ha : d93137 p = 1) (hb : d125009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36637 q ha hb
    | true =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93079 q = 1) (hb : d124930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93079, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93079, d124930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93100 q = 1) (hb : d124956 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93100, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93100, d124956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93137 q = 1) (hb : d125009 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93137, d125009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93137, d125009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36656 (p : Pattern) (ha : d93142 p = 1) (hb : d125015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36637 q ha hb
    | true =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93078 q = 1) (hb : d124929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93078, d124929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93106 q = 1) (hb : d124964 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93106, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93106, d124964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93107 q = 1) (hb : d124965 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93107, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93107, d124965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93142 q = 1) (hb : d125015 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93142, d125015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93142, d125015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36657 (p : Pattern) (ha : d93146 p = 1) (hb : d125020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93115 q = 1) (hb : d124979 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93115, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36648 q ha hb
    | true =>
      simp only [d93115, d124979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93116 q = 1) (hb : d124980 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93116, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93116, d124980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81906 q = 1) (hb : d124987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81906, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36646 q ha hb
    | true =>
      simp only [d81906, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81907 q = 1) (hb : d124988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81907, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81907, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93117 q = 1) (hb : d124989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93117, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93117, d124989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93118 q = 1) (hb : d124990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93118, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93118, d124990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93119 q = 1) (hb : d124991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93119, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93119, d124991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93146 q = 1) (hb : d125020 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93146, d125020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93146, d125020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36658 (p : Pattern) (ha : d93147 p = 1) (hb : d125021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81906 q = 1) (hb : d124987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81906, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36646 q ha hb
    | true =>
      simp only [d81906, d124987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81907 q = 1) (hb : d124988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81907, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81907, d124988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53376 q = 1) (hb : d124927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36627 q ha hb
    | true =>
      simp only [d53376, d124927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d124928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53377, d124928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93121 q = 1) (hb : d124993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93121, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93121, d124993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93122 q = 1) (hb : d124994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93122, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93122, d124994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93123 q = 1) (hb : d124995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93123, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93123, d124995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93147 q = 1) (hb : d125021 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93147, d125021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93147, d125021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36659 (p : Pattern) (ha : d93150 p = 1) (hb : d125024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93076 q = 1) (hb : d124923 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36637 q ha hb
    | true =>
      simp only [d93076, d124923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93077 q = 1) (hb : d124924 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93077, d124924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93127 q = 1) (hb : d124999 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93127, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93127, d124999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93128 q = 1) (hb : d125000 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93128, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93128, d125000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93129 q = 1) (hb : d125001 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93129, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93129, d125001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93150 q = 1) (hb : d125024 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93150, d125024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93150, d125024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36660 (p : Pattern) (ha : d93156 p = 1) (hb : d125030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93102 q = 1) (hb : d124960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93102, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36644 q ha hb
    | true =>
      simp only [d93102, d124960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36642 q ha hb
  have h2 (q : Pattern) (ha : d93103 q = 1) (hb : d124961 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93103, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93103, d124961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93104 q = 1) (hb : d124962 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93104, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93104, d124962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93105 q = 1) (hb : d124963 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93105, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93105, d124963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93109 q = 1) (hb : d124970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93109, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36645 q ha hb
    | true =>
      simp only [d93109, d124970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36643 q ha hb
  have h6 (q : Pattern) (ha : d93110 q = 1) (hb : d124971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93110, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93110, d124971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93111 q = 1) (hb : d124972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93111, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93111, d124972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93125 q = 1) (hb : d124997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93125, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36649 q ha hb
    | true =>
      simp only [d93125, d124997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36650 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d93082 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d93126 q = 1) (hb : d124998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93126, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93126, d124998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d93131 q = 1) (hb : d125003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93131, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36651 q ha hb
    | true =>
      simp only [d93131, d125003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d93132 q = 1) (hb : d125004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93132, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93132, d125004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d93133 q = 1) (hb : d125005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93133, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93133, d125005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93134 q = 1) (hb : d125006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93134, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93134, d125006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93135 q = 1) (hb : d125007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93135, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93135, d125007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93138 q = 1) (hb : d125011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93138, d125011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36655 q ha hb
    | true =>
      simp only [d93138, d125011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36653 q ha hb
  have h17 (q : Pattern) (ha : d93139 q = 1) (hb : d125012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93139, d125012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93139, d125012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93140 q = 1) (hb : d125013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93140, d125013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93140, d125013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d93141 q = 1) (hb : d125014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93141, d125014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93141, d125014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d93143 q = 1) (hb : d125017 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93143, d125017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36656 q ha hb
    | true =>
      simp only [d93143, d125017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36654 q ha hb
  have h21 (q : Pattern) (ha : d93144 q = 1) (hb : d125018 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93144, d125018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93144, d125018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d93145 q = 1) (hb : d125019 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93145, d125019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d93145, d125019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d93148 q = 1) (hb : d125022 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93148, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36657 q ha hb
    | true =>
      simp only [d93148, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36658 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d93091 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d93149 q = 1) (hb : d125023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d93149, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d93151 q = 1) (hb : d125025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93151, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36659 q ha hb
    | true =>
      simp only [d93151, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d93152 q = 1) (hb : d125026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93152, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d93152, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d93153 q = 1) (hb : d125027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d93153, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d93154 q = 1) (hb : d125028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93154, d125028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d93154, d125028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d93155 q = 1) (hb : d125029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93155, d125029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93155, d125029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d93156 q = 1) (hb : d125030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93156, d125030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93156, d125030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro36661 (p : Pattern) (ha : d93163 p = 1) (hb : d125042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93158 q = 1) (hb : d125032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93158, d125032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36650 q ha hb
    | true =>
      simp only [d93158, d125032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36628 q ha hb
  have h2 (q : Pattern) (ha : d93159 q = 1) (hb : d125033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93159, d125033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93159, d125033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93160 q = 1) (hb : d125034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93160, d125034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93160, d125034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93161 q = 1) (hb : d125035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93161, d125035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93161, d125035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93162 q = 1) (hb : d125036 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93162, d125036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93162, d125036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53470 q = 1) (hb : d125037 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53470, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36628 q ha hb
    | true =>
      simp only [d53470, d125037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53471 q = 1) (hb : d125038 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53471, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53471, d125038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53472 q = 1) (hb : d125039 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53472, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53472, d125039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53473 q = 1) (hb : d125040 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53473, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53473, d125040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53474 q = 1) (hb : d125041 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53474, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53474, d125041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93163 q = 1) (hb : d125042 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93163, d125042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93163, d125042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36662 (p : Pattern) (ha : d93170 p = 1) (hb : d125055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93148 q = 1) (hb : d125022 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93148, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36657 q ha hb
    | true =>
      simp only [d93148, d125022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36658 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93091 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93149 q = 1) (hb : d125023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93149, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93149, d125023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d93151 q = 1) (hb : d125025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93151, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36659 q ha hb
    | true =>
      simp only [d93151, d125025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93152 q = 1) (hb : d125026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93152, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93152, d125026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93153 q = 1) (hb : d125027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93153, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93153, d125027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93168 q = 1) (hb : d125053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93168, d125053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93168, d125053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93169 q = 1) (hb : d125054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93169, d125054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93169, d125054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93170 q = 1) (hb : d125055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93170, d125055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93170, d125055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36663 (p : Pattern) (ha : d53516 p = 1) (hb : d125063 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2335 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
  have h2 (q : Pattern) (ha : d2035 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro262 q ha hb
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2336 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2036 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2337 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2338 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15769 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15769, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15769, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d53516 q = 1) (hb : d125063 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d53516, d125063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d53516, d125063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro36664 (p : Pattern) (ha : d81951 p = 1) (hb : d125082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53522 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53522, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36663 q ha hb
    | true =>
      simp only [d53522, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36632 q ha hb
  have h2 (q : Pattern) (ha : d53523 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53523, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53523, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53524 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53524, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53524, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81949 q = 1) (hb : d125072 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81949, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81949, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d76367 q = 1) (hb : d125077 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76367, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35018 q ha hb
    | true =>
      simp only [d76367, d125077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10915 q hb ha
  have h6 (q : Pattern) (ha : d76368 q = 1) (hb : d125078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76368, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76368, d125078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d76369 q = 1) (hb : d125079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76369, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76369, d125079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76370 q = 1) (hb : d125080 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76370, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d76370, d125080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d81950 q = 1) (hb : d125081 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81950, d125081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81950, d125081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d81951 q = 1) (hb : d125082 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81951, d125082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81951, d125082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36665 (p : Pattern) (ha : d15768 p = 1) (hb : d53510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2331 q = 1) (hb : d53496 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, d53496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
  have h2 (q : Pattern) (ha : d2144 q = 1) (hb : d53423 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro289 q ha hb
    | true =>
      simp only [d2144, d53423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2332 q = 1) (hb : d53497 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2332, d53497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2145 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2145, d53424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2333 q = 1) (hb : d53498 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2333, d53498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2334 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2334, d53499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15767 q = 1) (hb : d53504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15767, d53504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15767, d53504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15768 q = 1) (hb : d53510 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15768, d53510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15768, d53510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro36666 (p : Pattern) (ha : d93178 p = 1) (hb : d125074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53517 q = 1) (hb : d125064 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53517, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36665 q hb ha
    | true =>
      simp only [d53517, d125064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36663 q ha hb
  have h2 (q : Pattern) (ha : d53518 q = 1) (hb : d125065 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53518, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53518, d125065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53519 q = 1) (hb : d125066 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53519, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53519, d125066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93176 q = 1) (hb : d125067 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d93176, d125067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93176, d125067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53522 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53522, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36663 q ha hb
    | true =>
      simp only [d53522, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36632 q ha hb
  have h6 (q : Pattern) (ha : d53523 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53523, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53523, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53524 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53524, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53524, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81949 q = 1) (hb : d125072 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81949, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d81949, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d93177 q = 1) (hb : d125073 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93177, d125073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93177, d125073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93178 q = 1) (hb : d125074 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93178, d125074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93178, d125074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36667 (p : Pattern) (ha : d93184 p = 1) (hb : d125088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93179 q = 1) (hb : d125075 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93179, d125075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36666 q ha hb
    | true =>
      simp only [d93179, d125075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93180 q = 1) (hb : d125076 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93180, d125076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93180, d125076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81952 q = 1) (hb : d125083 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81952, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36664 q ha hb
    | true =>
      simp only [d81952, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81953 q = 1) (hb : d125084 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81953, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81953, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93181 q = 1) (hb : d125085 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93181, d125085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93181, d125085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93182 q = 1) (hb : d125086 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93182, d125086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93182, d125086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93183 q = 1) (hb : d125087 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93183, d125087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93183, d125087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93184 q = 1) (hb : d125088 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93184, d125088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93184, d125088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36668 (p : Pattern) (ha : d93188 p = 1) (hb : d125100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81952 q = 1) (hb : d125083 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81952, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36664 q ha hb
    | true =>
      simp only [d81952, d125083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81953 q = 1) (hb : d125084 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81953, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81953, d125084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53551 q = 1) (hb : d125095 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53551, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36633 q ha hb
    | true =>
      simp only [d53551, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53552 q = 1) (hb : d125096 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53552, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53552, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93185 q = 1) (hb : d125097 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93185, d125097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93185, d125097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93186 q = 1) (hb : d125098 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93186, d125098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93186, d125098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d93187 q = 1) (hb : d125099 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93187, d125099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93187, d125099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d93188 q = 1) (hb : d125100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93188, d125100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d93188, d125100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36669 (p : Pattern) (ha : d93191 p = 1) (hb : d125104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53522 q = 1) (hb : d125069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53522, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36663 q ha hb
    | true =>
      simp only [d53522, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36632 q ha hb
  have h2 (q : Pattern) (ha : d53523 q = 1) (hb : d125070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53523, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53523, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53524 q = 1) (hb : d125071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53524, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53524, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81949 q = 1) (hb : d125072 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81949, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81949, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53532 q = 1) (hb : d125089 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53532, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36632 q ha hb
    | true =>
      simp only [d53532, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28887 q hb ha
  have h6 (q : Pattern) (ha : d53533 q = 1) (hb : d125090 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53533, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53533, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53534 q = 1) (hb : d125091 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53534, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53534, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53540 q = 1) (hb : d125092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53540, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53540, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d93190 q = 1) (hb : d125103 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d93190, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93190, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93191 q = 1) (hb : d125104 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d93191, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d93191, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro36670 (p : Pattern) (ha : d93203 p = 1) (hb : d125110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93192 q = 1) (hb : d125105 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d93192, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36669 q ha hb
    | true =>
      simp only [d93192, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93193 q = 1) (hb : d125106 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d93193, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93193, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93200 q = 1) (hb : d125107 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d93200, d125107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93200, d125107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93201 q = 1) (hb : d125108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d93201, d125108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93201, d125108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93202 q = 1) (hb : d125109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d93202, d125109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93202, d125109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93203 q = 1) (hb : d125110 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d93203, d125110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93203, d125110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36671 (p : Pattern) (ha : d93209 p = 1) (hb : d125116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93189 q = 1) (hb : d125101 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93189, d125101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36667 q ha hb
    | true =>
      simp only [d93189, d125101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36668 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d93198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d93199 q = 1) (hb : d125102 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93199, d125102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93199, d125102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d93204 q = 1) (hb : d125111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d93204, d125111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36670 q ha hb
    | true =>
      simp only [d93204, d125111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93205 q = 1) (hb : d125112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d93205, d125112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93205, d125112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93206 q = 1) (hb : d125113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93206, d125113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93206, d125113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93207 q = 1) (hb : d125114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93207, d125114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93207, d125114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93208 q = 1) (hb : d125115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93208, d125115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93208, d125115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93209 q = 1) (hb : d125116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93209, d125116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93209, d125116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro36672 (p : Pattern) (ha : d93215 p = 1) (hb : d125133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93088 q = 1) (hb : d124943 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93088, d124943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93088, d124943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36639 q ha hb
  have h2 (q : Pattern) (ha : d93089 q = 1) (hb : d124944 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93089, d124944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93089, d124944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93097 q = 1) (hb : d124953 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93097, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36639 q ha hb
    | true =>
      simp only [d93097, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36641 q ha hb
  have h4 (q : Pattern) (ha : d93098 q = 1) (hb : d124954 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93098, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93098, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93099 q = 1) (hb : d124955 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93099, d124955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93099, d124955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93157 q = 1) (hb : d125031 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93157, d125031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36652 q ha hb
    | true =>
      simp only [d93157, d125031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36660 q ha hb
  have h7 (q : Pattern) (ha : d93164 q = 1) (hb : d125049 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93164, d125049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36661 q ha hb
    | true =>
      simp only [d93164, d125049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36630 q ha hb
  have h8 (q : Pattern) (ha : d93165 q = 1) (hb : d125050 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93165, d125050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93165, d125050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93166 q = 1) (hb : d125051 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93166, d125051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93166, d125051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d93167 q = 1) (hb : d125052 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93167, d125052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93167, d125052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93171 q = 1) (hb : d125056 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93171, d125056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93171, d125056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36662 q ha hb
  have h12 (q : Pattern) (ha : d53491 q = 1) (hb : d125058 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53491, d125058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53491, d125058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36631 q ha hb
  have h13 (q : Pattern) (ha : d93172 q = 1) (hb : d125059 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93172, d125059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d93172, d125059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93173 q = 1) (hb : d125060 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93173, d125060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93173, d125060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d93174 q = 1) (hb : d125061 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93174, d125061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d93174, d125061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d93175 q = 1) (hb : d125062 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93175, d125062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93175, d125062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93210 q = 1) (hb : d125117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d93210, d125117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93210, d125117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36671 q ha hb
  have h18 (q : Pattern) (ha : d53577 q = 1) (hb : d125128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53577, d125128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53577, d125128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36635 q ha hb
  have h19 (q : Pattern) (ha : d93211 q = 1) (hb : d125129 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d93211, d125129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d93211, d125129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d93212 q = 1) (hb : d125130 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d93212, d125130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d93212, d125130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d93213 q = 1) (hb : d125131 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93213, d125131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d93213, d125131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d93214 q = 1) (hb : d125132 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d93214, d125132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d93214, d125132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d93215 q = 1) (hb : d125133 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d93215, d125133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d93215, d125133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36673 (p : Pattern) (ha : d93221 p = 1) (hb : d125139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93216 q = 1) (hb : d125134 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d93216, d125134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93216, d125134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36672 q ha hb
  have h2 (q : Pattern) (ha : d93217 q = 1) (hb : d125135 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d93217, d125135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93217, d125135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d93218 q = 1) (hb : d125136 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d93218, d125136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93218, d125136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d93219 q = 1) (hb : d125137 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d93219, d125137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93219, d125137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d93220 q = 1) (hb : d125138 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d93220, d125138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93220, d125138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d93221 q = 1) (hb : d125139 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d93221, d125139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93221, d125139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36674 (p : Pattern) (ha : d93227 p = 1) (hb : d125145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d92620 q = 1) (hb : d124246 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92620, d124246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36439 q ha hb
    | true =>
      simp only [d92620, d124246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36481 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92769 q = 1) (hb : d124440 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92769, d124440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92769, d124440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36529 q ha hb
  have h3 (q : Pattern) (ha : d92770 q = 1) (hb : d124441 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92770, d124441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d92770, d124441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92919 q = 1) (hb : d124673 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d92919, d124673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92919, d124673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36577 q ha hb
  have h5 (q : Pattern) (ha : d92920 q = 1) (hb : d124674 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d92920, d124674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92920, d124674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92921 q = 1) (hb : d124675 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d92921, d124675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92921, d124675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93070 q = 1) (hb : d124907 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93070, d124907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93070, d124907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36625 q ha hb
  have h8 (q : Pattern) (ha : d93071 q = 1) (hb : d124908 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93071, d124908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93071, d124908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d93072 q = 1) (hb : d124909 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93072, d124909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93072, d124909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d93073 q = 1) (hb : d124910 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93073, d124910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d93073, d124910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d93222 q = 1) (hb : d125140 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d93222, d125140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93222, d125140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36673 q ha hb
  have h12 (q : Pattern) (ha : d93223 q = 1) (hb : d125141 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d93223, d125141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93223, d125141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d93224 q = 1) (hb : d125142 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d93224, d125142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93224, d125142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d93225 q = 1) (hb : d125143 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d93225, d125143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d93225, d125143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d93226 q = 1) (hb : d125144 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d93226, d125144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d93226, d125144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d93227 q = 1) (hb : d125145 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d93227, d125145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d93227, d125145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro36675 (p : Pattern) (ha : d93233 p = 1) (hb : d125151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93228 q = 1) (hb : d125146 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d93228, d125146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36674 q ha hb
    | true =>
      simp only [d93228, d125146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93229 q = 1) (hb : d125147 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d93229, d125147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93229, d125147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93230 q = 1) (hb : d125148 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d93230, d125148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93230, d125148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93231 q = 1) (hb : d125149 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d93231, d125149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93231, d125149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93232 q = 1) (hb : d125150 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d93232, d125150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93232, d125150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93233 q = 1) (hb : d125151 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d93233, d125151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93233, d125151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36676 (p : Pattern) (ha : d93239 p = 1) (hb : d125157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93234 q = 1) (hb : d125152 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d93234, d125152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36675 q ha hb
    | true =>
      simp only [d93234, d125152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93235 q = 1) (hb : d125153 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d93235, d125153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93235, d125153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93236 q = 1) (hb : d125154 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d93236, d125154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93236, d125154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93237 q = 1) (hb : d125155 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d93237, d125155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93237, d125155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93238 q = 1) (hb : d125156 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d93238, d125156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93238, d125156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93239 q = 1) (hb : d125157 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d93239, d125157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93239, d125157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36677 (p : Pattern) (ha : d93245 p = 1) (hb : d125163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93240 q = 1) (hb : d125158 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d93240, d125158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36676 q ha hb
    | true =>
      simp only [d93240, d125158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93241 q = 1) (hb : d125159 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d93241, d125159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93241, d125159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93242 q = 1) (hb : d125160 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d93242, d125160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93242, d125160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93243 q = 1) (hb : d125161 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d93243, d125161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93243, d125161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93244 q = 1) (hb : d125162 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d93244, d125162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93244, d125162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93245 q = 1) (hb : d125163 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d93245, d125163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93245, d125163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36678 (p : Pattern) (ha : d93251 p = 1) (hb : d125169 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93246 q = 1) (hb : d125164 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d93246, d125164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36677 q ha hb
    | true =>
      simp only [d93246, d125164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93247 q = 1) (hb : d125165 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d93247, d125165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93247, d125165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93248 q = 1) (hb : d125166 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d93248, d125166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93248, d125166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93249 q = 1) (hb : d125167 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d93249, d125167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93249, d125167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93250 q = 1) (hb : d125168 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d93250, d125168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93250, d125168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93251 q = 1) (hb : d125169 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d93251, d125169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93251, d125169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36679 (p : Pattern) (ha : d93257 p = 1) (hb : d125175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93252 q = 1) (hb : d125170 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d93252, d125170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36678 q ha hb
    | true =>
      simp only [d93252, d125170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93253 q = 1) (hb : d125171 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d93253, d125171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93253, d125171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93254 q = 1) (hb : d125172 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d93254, d125172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93254, d125172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93255 q = 1) (hb : d125173 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d93255, d125173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93255, d125173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93256 q = 1) (hb : d125174 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d93256, d125174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93256, d125174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93257 q = 1) (hb : d125175 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d93257, d125175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93257, d125175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36680 (p : Pattern) (ha : d93263 p = 1) (hb : d125181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93258 q = 1) (hb : d125176 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d93258, d125176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36679 q ha hb
    | true =>
      simp only [d93258, d125176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93259 q = 1) (hb : d125177 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d93259, d125177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93259, d125177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93260 q = 1) (hb : d125178 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d93260, d125178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93260, d125178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93261 q = 1) (hb : d125179 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d93261, d125179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93261, d125179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93262 q = 1) (hb : d125180 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d93262, d125180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93262, d125180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93263 q = 1) (hb : d125181 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d93263, d125181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93263, d125181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36681 (p : Pattern) (ha : d93269 p = 1) (hb : d125187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d93264 q = 1) (hb : d125182 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d93264, d125182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36680 q ha hb
    | true =>
      simp only [d93264, d125182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d93265 q = 1) (hb : d125183 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d93265, d125183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d93265, d125183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d93266 q = 1) (hb : d125184 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d93266, d125184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d93266, d125184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d93267 q = 1) (hb : d125185 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d93267, d125185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93267, d125185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d93268 q = 1) (hb : d125186 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d93268, d125186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d93268, d125186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d93269 q = 1) (hb : d125187 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d93269, d125187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d93269, d125187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36682 (p : Pattern) (ha : d122306 p = 1) (hb : d163447 p = 1) : d125190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d122306 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14001 q = 1) (hb : d122306 q = 1) : d123899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36164 q ha hb
    | true =>
      simp only [d14001, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14057 q = 1) (hb : d122306 q = 1) : d123954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14058 q = 1) (hb : d122306 q = 1) : d123955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14058, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14059 q = 1) (hb : d122306 q = 1) : d123956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14060 q = 1) (hb : d122306 q = 1) : d123957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163447 q = 1) : d125190 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163447, d125190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163447, d125190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro36683 (p : Pattern) (ha : d122306 p = 1) (hb : d163457 p = 1) : d125200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d122306 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14033 q = 1) (hb : d122306 q = 1) : d123930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36168 q ha hb
    | true =>
      simp only [d14033, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163453 q = 1) : d125196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163453, d125196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163453, d125196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163454 q = 1) : d125197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163454, d125197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163454, d125197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163455 q = 1) : d125198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163455, d125198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163455, d125198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163456 q = 1) : d125199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163456, d125199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163456, d125199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163457 q = 1) : d125200 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163457, d125200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163457, d125200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro36684 (p : Pattern) (ha : d122306 p = 1) (hb : d163463 p = 1) : d125206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14062 q = 1) (hb : d122306 q = 1) : d123959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36171 q ha hb
    | true =>
      simp only [d14062, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36172 q ha hb
  have h2 (q : Pattern) (ha : d14063 q = 1) (hb : d122306 q = 1) : d123960 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14063, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163445 q = 1) : d125188 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163445, d125188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163445, d125188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163446 q = 1) : d125189 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163446, d125189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163446, d125189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163448 q = 1) : d125191 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163448, d125191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163448, d125191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36682 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163449 q = 1) : d125192 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163449, d125192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163449, d125192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163450 q = 1) : d125193 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163450, d125193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163450, d125193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d163451 q = 1) : d125194 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163451, d125194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163451, d125194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d163452 q = 1) : d125195 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163452, d125195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163452, d125195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d163458 q = 1) : d125201 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163458, d125201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163458, d125201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36683 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d163459 q = 1) : d125202 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163459, d125202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163459, d125202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d163460 q = 1) : d125203 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163460, d125203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163460, d125203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d163461 q = 1) : d125204 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163461, d125204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163461, d125204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d163462 q = 1) : d125205 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163462, d125205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163462, d125205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d163463 q = 1) : d125206 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163463, d125206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163463, d125206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36685 (p : Pattern) (ha : d122306 p = 1) (hb : d163469 p = 1) : d125212 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d122306 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163464 q = 1) : d125207 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163464, d125207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163464, d125207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36684 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163465 q = 1) : d125208 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163465, d125208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163465, d125208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163466 q = 1) : d125209 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163466, d125209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163466, d125209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163467 q = 1) : d125210 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163467, d125210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163467, d125210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163468 q = 1) : d125211 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163468, d125211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163468, d125211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163469 q = 1) : d125212 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163469, d125212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163469, d125212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro36686 (p : Pattern) (ha : d122306 p = 1) (hb : d163472 p = 1) : d125215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14235 q = 1) (hb : d122306 q = 1) : d124091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36197 q ha hb
    | true =>
      simp only [d14235, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36198 q ha hb
  have h2 (q : Pattern) (ha : d14236 q = 1) (hb : d122306 q = 1) : d124092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14236, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14237 q = 1) (hb : d122306 q = 1) : d124093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14237, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14238 q = 1) (hb : d122306 q = 1) : d124094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14239 q = 1) (hb : d122306 q = 1) : d124095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163472 q = 1) : d125215 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163472, d125215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163472, d125215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36687 (p : Pattern) (ha : d122306 p = 1) (hb : d163483 p = 1) : d125226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163478 q = 1) : d125221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163478, d125221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36225 q hb ha
    | true =>
      simp only [d163478, d125221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36204 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163479 q = 1) : d125222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163479, d125222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163479, d125222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163480 q = 1) : d125223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163480, d125223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163480, d125223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163481 q = 1) : d125224 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163481, d125224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163481, d125224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163482 q = 1) : d125225 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163482, d125225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163482, d125225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163483 q = 1) : d125226 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163483, d125226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163483, d125226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36688 (p : Pattern) (ha : d122306 p = 1) (hb : d163489 p = 1) : d125232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14241 q = 1) (hb : d122306 q = 1) : d124097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36196 q ha hb
    | true =>
      simp only [d14241, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36199 q ha hb
  have h2 (q : Pattern) (ha : d14242 q = 1) (hb : d122306 q = 1) : d124098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14242, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163470 q = 1) : d125213 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163470, d125213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163470, d125213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163471 q = 1) : d125214 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163471, d125214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163471, d125214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163473 q = 1) : d125216 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163473, d125216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163473, d125216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36686 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163474 q = 1) : d125217 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163474, d125217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163474, d125217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163475 q = 1) : d125218 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163475, d125218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163475, d125218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d163476 q = 1) : d125219 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163476, d125219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163476, d125219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d163477 q = 1) : d125220 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163477, d125220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163477, d125220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d163484 q = 1) : d125227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163484, d125227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163484, d125227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36687 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d163485 q = 1) : d125228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163485, d125228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163485, d125228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d163486 q = 1) : d125229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163486, d125229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163486, d125229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d163487 q = 1) : d125230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163487, d125230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163487, d125230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d163488 q = 1) : d125231 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163488, d125231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163488, d125231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d163489 q = 1) : d125232 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163489, d125232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163489, d125232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36689 (p : Pattern) (ha : d122306 p = 1) (hb : d163495 p = 1) : d125238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163490 q = 1) : d125233 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163490, d125233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163490, d125233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36688 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163491 q = 1) : d125234 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163491, d125234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163491, d125234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163492 q = 1) : d125235 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163492, d125235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163492, d125235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163493 q = 1) : d125236 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163493, d125236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163493, d125236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163494 q = 1) : d125237 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163494, d125237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163494, d125237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163495 q = 1) : d125238 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163495, d125238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163495, d125238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36690 (p : Pattern) (ha : d122306 p = 1) (hb : d163499 p = 1) : d125242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14502 q = 1) (hb : d122306 q = 1) : d124277 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36235 q ha hb
    | true =>
      simp only [d14502, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36236 q ha hb
  have h2 (q : Pattern) (ha : d14503 q = 1) (hb : d122306 q = 1) : d124278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14503, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14504 q = 1) (hb : d122306 q = 1) : d124279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14504, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14505 q = 1) (hb : d122306 q = 1) : d124280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14506 q = 1) (hb : d122306 q = 1) : d124281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163499 q = 1) : d125242 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163499, d125242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163499, d125242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36691 (p : Pattern) (ha : d122306 p = 1) (hb : d163510 p = 1) : d125253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163505 q = 1) : d125248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163505, d125248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36263 q hb ha
    | true =>
      simp only [d163505, d125248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36242 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163506 q = 1) : d125249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163506, d125249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163506, d125249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163507 q = 1) : d125250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163507, d125250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163507, d125250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163508 q = 1) : d125251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163508, d125251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163508, d125251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163509 q = 1) : d125252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163509, d125252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163509, d125252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163510 q = 1) : d125253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163510, d125253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163510, d125253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36692 (p : Pattern) (ha : d122306 p = 1) (hb : d163516 p = 1) : d125259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14508 q = 1) (hb : d122306 q = 1) : d124283 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36234 q ha hb
    | true =>
      simp only [d14508, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36237 q ha hb
  have h2 (q : Pattern) (ha : d14509 q = 1) (hb : d122306 q = 1) : d124284 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14509, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163497 q = 1) : d125240 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163497, d125240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163497, d125240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163498 q = 1) : d125241 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163498, d125241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163498, d125241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163500 q = 1) : d125243 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163500, d125243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163500, d125243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36690 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163501 q = 1) : d125244 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163501, d125244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163501, d125244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163502 q = 1) : d125245 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163502, d125245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163502, d125245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d163503 q = 1) : d125246 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163503, d125246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163503, d125246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d163504 q = 1) : d125247 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163504, d125247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163504, d125247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d163511 q = 1) : d125254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163511, d125254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163511, d125254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36691 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d163512 q = 1) : d125255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163512, d125255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163512, d125255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d163513 q = 1) : d125256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163513, d125256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163513, d125256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d163514 q = 1) : d125257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163514, d125257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163514, d125257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d163515 q = 1) : d125258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163515, d125258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163515, d125258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d163516 q = 1) : d125259 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163516, d125259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163516, d125259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36693 (p : Pattern) (ha : d122306 p = 1) (hb : d163522 p = 1) : d125265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163517 q = 1) : d125260 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163517, d125260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163517, d125260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36692 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163518 q = 1) : d125261 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163518, d125261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163518, d125261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163519 q = 1) : d125262 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163519, d125262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163519, d125262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163520 q = 1) : d125263 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163520, d125263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163520, d125263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163521 q = 1) : d125264 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163521, d125264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163521, d125264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163522 q = 1) : d125265 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163522, d125265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163522, d125265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36694 (p : Pattern) (ha : d122306 p = 1) (hb : d163527 p = 1) : d125270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14809 q = 1) (hb : d122306 q = 1) : d124478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36273 q ha hb
    | true =>
      simp only [d14809, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36274 q ha hb
  have h2 (q : Pattern) (ha : d14810 q = 1) (hb : d122306 q = 1) : d124479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14810, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14811 q = 1) (hb : d122306 q = 1) : d124480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14811, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14812 q = 1) (hb : d122306 q = 1) : d124481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14813 q = 1) (hb : d122306 q = 1) : d124482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163527 q = 1) : d125270 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163527, d125270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163527, d125270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36695 (p : Pattern) (ha : d122306 p = 1) (hb : d163534 p = 1) : d124637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34634 q ha hb
    | true =>
      simp only [d15016, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15027 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15028 q = 1) (hb : d122306 q = 1) : d124605 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, d122306, d124605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15043 q = 1) (hb : d122305 q = 1) : d124622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15043, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34608 q ha hb
    | true =>
      simp only [d15043, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34609 q ha hb
  have h7 (q : Pattern) (ha : d15044 q = 1) (hb : d122305 q = 1) : d124623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15044, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15044, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15045 q = 1) (hb : d122305 q = 1) : d124624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15046 q = 1) (hb : d122306 q = 1) : d124625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, d122306, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15046, d122306, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d163533 q = 1) : d124636 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163533, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d163533, d124636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d163534 q = 1) : d124637 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163534, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163534, d124637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro36696 (p : Pattern) (ha : d122306 p = 1) (hb : d163540 p = 1) : d125279 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163535 q = 1) : d124638 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163535, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36695 q ha hb
    | true =>
      simp only [d163535, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163536 q = 1) : d124639 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163536, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163536, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d122306 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36281 q ha hb
    | true =>
      simp only [d15049, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d122306 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163537 q = 1) : d125276 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163537, d125276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163537, d125276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163538 q = 1) : d125277 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163538, d125277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163538, d125277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163539 q = 1) : d125278 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163539, d125278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163539, d125278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d163540 q = 1) : d125279 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163540, d125279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163540, d125279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36697 (p : Pattern) (ha : d122306 p = 1) (hb : d163546 p = 1) : d125285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163541 q = 1) : d125280 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163541, d125280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36696 q ha hb
    | true =>
      simp only [d163541, d125280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36282 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163542 q = 1) : d125281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163542, d125281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163542, d125281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163543 q = 1) : d125282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163543, d125282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163543, d125282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163544 q = 1) : d125283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163544, d125283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163544, d125283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163545 q = 1) : d125284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163545, d125284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163545, d125284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163546 q = 1) : d125285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163546, d125285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163546, d125285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36698 (p : Pattern) (ha : d122306 p = 1) (hb : d163552 p = 1) : d125291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14815 q = 1) (hb : d122306 q = 1) : d124484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36272 q ha hb
    | true =>
      simp only [d14815, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36275 q ha hb
  have h2 (q : Pattern) (ha : d14816 q = 1) (hb : d122306 q = 1) : d124485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14816, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163525 q = 1) : d125268 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163525, d125268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163525, d125268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163526 q = 1) : d125269 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163526, d125269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163526, d125269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163528 q = 1) : d125271 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163528, d125271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163528, d125271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36694 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163529 q = 1) : d125272 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163529, d125272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163529, d125272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163530 q = 1) : d125273 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163530, d125273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163530, d125273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d163531 q = 1) : d125274 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163531, d125274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163531, d125274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d163532 q = 1) : d125275 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163532, d125275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163532, d125275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d163547 q = 1) : d125286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163547, d125286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163547, d125286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36697 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d163548 q = 1) : d125287 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163548, d125287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163548, d125287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d163549 q = 1) : d125288 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163549, d125288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163549, d125288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d163550 q = 1) : d125289 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163550, d125289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163550, d125289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d163551 q = 1) : d125290 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163551, d125290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163551, d125290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d163552 q = 1) : d125291 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163552, d125291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163552, d125291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36699 (p : Pattern) (ha : d122306 p = 1) (hb : d163558 p = 1) : d125297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163553 q = 1) : d125292 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163553, d125292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163553, d125292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36698 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163554 q = 1) : d125293 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163554, d125293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163554, d125293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163555 q = 1) : d125294 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163555, d125294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163555, d125294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163556 q = 1) : d125295 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163556, d125295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163556, d125295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163557 q = 1) : d125296 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163557, d125296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163557, d125296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163558 q = 1) : d125297 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163558, d125297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163558, d125297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36700 (p : Pattern) (ha : d122306 p = 1) (hb : d163564 p = 1) : d125303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15202 q = 1) (hb : d122306 q = 1) : d124712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36316 q ha hb
    | true =>
      simp only [d15202, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36317 q ha hb
  have h2 (q : Pattern) (ha : d15203 q = 1) (hb : d122306 q = 1) : d124713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15204 q = 1) (hb : d122306 q = 1) : d124714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15204, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15205 q = 1) (hb : d122306 q = 1) : d124715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15206 q = 1) (hb : d122306 q = 1) : d124716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163564 q = 1) : d125303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163564, d125303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163564, d125303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36701 (p : Pattern) (ha : d122306 p = 1) (hb : d163571 p = 1) : d124871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d122305 q = 1) : d124836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34689 q ha hb
    | true =>
      simp only [d15409, d124836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d122305 q = 1) : d124837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d124837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d122305 q = 1) : d124838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d124838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15420 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15421 q = 1) (hb : d122306 q = 1) : d124839 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, d122306, d124839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15436 q = 1) (hb : d122305 q = 1) : d124856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34663 q ha hb
    | true =>
      simp only [d15436, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34664 q ha hb
  have h7 (q : Pattern) (ha : d15437 q = 1) (hb : d122305 q = 1) : d124857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15438 q = 1) (hb : d122305 q = 1) : d124858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15439 q = 1) (hb : d122306 q = 1) : d124859 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, d122306, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15439, d122306, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d163570 q = 1) : d124870 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163570, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d163570, d124870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d163571 q = 1) : d124871 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163571, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163571, d124871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro36702 (p : Pattern) (ha : d122306 p = 1) (hb : d163577 p = 1) : d125312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163572 q = 1) : d124872 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163572, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36701 q ha hb
    | true =>
      simp only [d163572, d124872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163573 q = 1) : d124873 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163573, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163573, d124873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d122306 q = 1) : d124862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36324 q ha hb
    | true =>
      simp only [d15442, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d122306 q = 1) : d124863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163574 q = 1) : d125309 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163574, d125309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163574, d125309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163575 q = 1) : d125310 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163575, d125310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163575, d125310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163576 q = 1) : d125311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163576, d125311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163576, d125311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d163577 q = 1) : d125312 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163577, d125312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163577, d125312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36703 (p : Pattern) (ha : d122306 p = 1) (hb : d163583 p = 1) : d125318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163578 q = 1) : d125313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163578, d125313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36702 q ha hb
    | true =>
      simp only [d163578, d125313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36325 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163579 q = 1) : d125314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163579, d125314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163579, d125314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163580 q = 1) : d125315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163580, d125315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163580, d125315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163581 q = 1) : d125316 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163581, d125316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163581, d125316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163582 q = 1) : d125317 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163582, d125317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163582, d125317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163583 q = 1) : d125318 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163583, d125318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163583, d125318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36704 (p : Pattern) (ha : d122306 p = 1) (hb : d163589 p = 1) : d125324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15208 q = 1) (hb : d122306 q = 1) : d124718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36315 q ha hb
    | true =>
      simp only [d15208, d124718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36318 q ha hb
  have h2 (q : Pattern) (ha : d15209 q = 1) (hb : d122306 q = 1) : d124719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15209, d124719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163562 q = 1) : d125301 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163562, d125301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163562, d125301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163563 q = 1) : d125302 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163563, d125302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163563, d125302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163565 q = 1) : d125304 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163565, d125304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163565, d125304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36700 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163566 q = 1) : d125305 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163566, d125305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163566, d125305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163567 q = 1) : d125306 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163567, d125306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163567, d125306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d163568 q = 1) : d125307 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163568, d125307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163568, d125307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d163569 q = 1) : d125308 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163569, d125308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163569, d125308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d163584 q = 1) : d125319 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163584, d125319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163584, d125319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36703 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d163585 q = 1) : d125320 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163585, d125320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163585, d125320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d163586 q = 1) : d125321 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163586, d125321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163586, d125321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d163587 q = 1) : d125322 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163587, d125322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163587, d125322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d163588 q = 1) : d125323 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163588, d125323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163588, d125323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d163589 q = 1) : d125324 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163589, d125324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163589, d125324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36705 (p : Pattern) (ha : d122306 p = 1) (hb : d163595 p = 1) : d125330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163590 q = 1) : d125325 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163590, d125325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163590, d125325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36704 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163591 q = 1) : d125326 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163591, d125326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163591, d125326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163592 q = 1) : d125327 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163592, d125327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163592, d125327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163593 q = 1) : d125328 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163593, d125328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163593, d125328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163594 q = 1) : d125329 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163594, d125329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163594, d125329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163595 q = 1) : d125330 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163595, d125330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163595, d125330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36706 (p : Pattern) (ha : d122306 p = 1) (hb : d163602 p = 1) : d125337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15594 q = 1) (hb : d122306 q = 1) : d124947 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36359 q ha hb
    | true =>
      simp only [d15594, d124947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36360 q ha hb
  have h2 (q : Pattern) (ha : d15595 q = 1) (hb : d122306 q = 1) : d124948 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, d124948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15596 q = 1) (hb : d122306 q = 1) : d124949 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15596, d124949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15597 q = 1) (hb : d122306 q = 1) : d124950 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d124950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15598 q = 1) (hb : d122306 q = 1) : d124951 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d124951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163602 q = 1) : d125337 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163602, d125337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163602, d125337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36707 (p : Pattern) (ha : d122306 p = 1) (hb : d163609 p = 1) : d125104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d122305 q = 1) : d125069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34742 q ha hb
    | true =>
      simp only [d15787, d125069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d122305 q = 1) : d125070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d125070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d122305 q = 1) : d125071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d125071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d15798 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d15799 q = 1) (hb : d122306 q = 1) : d125072 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, d122306, d125072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d15814 q = 1) (hb : d122305 q = 1) : d125089 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34718 q ha hb
    | true =>
      simp only [d15814, d125089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34719 q ha hb
  have h7 (q : Pattern) (ha : d15815 q = 1) (hb : d122305 q = 1) : d125090 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, d125090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15816 q = 1) (hb : d122305 q = 1) : d125091 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d125091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15817 q = 1) (hb : d122306 q = 1) : d125092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, d122306, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15817, d122306, d125092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d163608 q = 1) : d125103 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163608, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d163608, d125103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d163609 q = 1) : d125104 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163609, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163609, d125104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro36708 (p : Pattern) (ha : d122306 p = 1) (hb : d163615 p = 1) : d125346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163610 q = 1) : d125105 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163610, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36707 q ha hb
    | true =>
      simp only [d163610, d125105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163611 q = 1) : d125106 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163611, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163611, d125106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d122306 q = 1) : d125095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36367 q ha hb
    | true =>
      simp only [d15820, d125095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d122306 q = 1) : d125096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d125096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163612 q = 1) : d125343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163612, d125343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163612, d125343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163613 q = 1) : d125344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163613, d125344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163613, d125344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163614 q = 1) : d125345 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163614, d125345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163614, d125345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d163615 q = 1) : d125346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163615, d125346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163615, d125346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36709 (p : Pattern) (ha : d122306 p = 1) (hb : d163621 p = 1) : d125352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163616 q = 1) : d125347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163616, d125347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36708 q ha hb
    | true =>
      simp only [d163616, d125347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36368 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163617 q = 1) : d125348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163617, d125348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163617, d125348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163618 q = 1) : d125349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163618, d125349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163618, d125349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163619 q = 1) : d125350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163619, d125350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163619, d125350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163620 q = 1) : d125351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163620, d125351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163620, d125351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163621 q = 1) : d125352 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163621, d125352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163621, d125352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36710 (p : Pattern) (ha : d122306 p = 1) (hb : d163627 p = 1) : d125358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15600 q = 1) (hb : d122306 q = 1) : d124953 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36358 q ha hb
    | true =>
      simp only [d15600, d124953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36361 q ha hb
  have h2 (q : Pattern) (ha : d15601 q = 1) (hb : d122306 q = 1) : d124954 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15601, d124954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163600 q = 1) : d125335 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163600, d125335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163600, d125335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163601 q = 1) : d125336 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163601, d125336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163601, d125336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163603 q = 1) : d125338 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163603, d125338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163603, d125338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36706 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163604 q = 1) : d125339 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163604, d125339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163604, d125339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163605 q = 1) : d125340 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163605, d125340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163605, d125340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d163606 q = 1) : d125341 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163606, d125341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163606, d125341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d163607 q = 1) : d125342 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163607, d125342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163607, d125342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d163622 q = 1) : d125353 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163622, d125353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163622, d125353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36709 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d163623 q = 1) : d125354 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163623, d125354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163623, d125354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d163624 q = 1) : d125355 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163624, d125355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163624, d125355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d163625 q = 1) : d125356 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163625, d125356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163625, d125356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d163626 q = 1) : d125357 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163626, d125357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163626, d125357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d163627 q = 1) : d125358 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163627, d125358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163627, d125358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36711 (p : Pattern) (ha : d122306 p = 1) (hb : d163633 p = 1) : d125364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163628 q = 1) : d125359 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163628, d125359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163628, d125359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36710 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163629 q = 1) : d125360 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163629, d125360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163629, d125360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163630 q = 1) : d125361 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163630, d125361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163630, d125361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163631 q = 1) : d125362 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163631, d125362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163631, d125362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163632 q = 1) : d125363 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163632, d125363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163632, d125363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163633 q = 1) : d125364 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163633, d125364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163633, d125364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36712 (p : Pattern) (ha : d122306 p = 1) (hb : d163639 p = 1) : d125370 p = 1 := by
  have h0 (q : Pattern) (ha : d122306 q = 1) (hb : d163496 q = 1) : d125239 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163496, d125239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36685 q ha hb
    | true =>
      simp only [d163496, d125239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36689 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163523 q = 1) : d125266 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163523, d125266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163523, d125266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36693 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163524 q = 1) : d125267 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163524, d125267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163524, d125267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163559 q = 1) : d125298 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163559, d125298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163559, d125298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36699 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163560 q = 1) : d125299 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163560, d125299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163560, d125299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163561 q = 1) : d125300 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163561, d125300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163561, d125300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d163596 q = 1) : d125331 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163596, d125331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163596, d125331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36705 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d163597 q = 1) : d125332 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163597, d125332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163597, d125332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d163598 q = 1) : d125333 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163598, d125333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163598, d125333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d163599 q = 1) : d125334 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d163599, d125334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163599, d125334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d163634 q = 1) : d125365 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163634, d125365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163634, d125365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36711 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d163635 q = 1) : d125366 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163635, d125366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163635, d125366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d163636 q = 1) : d125367 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163636, d125367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163636, d125367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d163637 q = 1) : d125368 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d163637, d125368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163637, d125368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d163638 q = 1) : d125369 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d163638, d125369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163638, d125369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d163639 q = 1) : d125370 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d163639, d125370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d163639, d125370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro36713 (p : Pattern) (ha : d122306 p = 1) (hb : d163645 p = 1) : d125376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163640 q = 1) : d125371 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d163640, d125371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36712 q ha hb
    | true =>
      simp only [d163640, d125371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163641 q = 1) : d125372 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d163641, d125372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163641, d125372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163642 q = 1) : d125373 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d163642, d125373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163642, d125373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163643 q = 1) : d125374 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d163643, d125374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163643, d125374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163644 q = 1) : d125375 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d163644, d125375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163644, d125375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163645 q = 1) : d125376 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d163645, d125376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163645, d125376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36714 (p : Pattern) (ha : d122306 p = 1) (hb : d163651 p = 1) : d125382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163646 q = 1) : d125377 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d163646, d125377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36713 q ha hb
    | true =>
      simp only [d163646, d125377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163647 q = 1) : d125378 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d163647, d125378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163647, d125378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163648 q = 1) : d125379 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d163648, d125379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163648, d125379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163649 q = 1) : d125380 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d163649, d125380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163649, d125380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163650 q = 1) : d125381 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d163650, d125381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163650, d125381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163651 q = 1) : d125382 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d163651, d125382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163651, d125382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36715 (p : Pattern) (ha : d122306 p = 1) (hb : d163657 p = 1) : d125388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163652 q = 1) : d125383 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d163652, d125383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36714 q ha hb
    | true =>
      simp only [d163652, d125383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163653 q = 1) : d125384 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d163653, d125384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163653, d125384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163654 q = 1) : d125385 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d163654, d125385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163654, d125385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163655 q = 1) : d125386 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d163655, d125386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163655, d125386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163656 q = 1) : d125387 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d163656, d125387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163656, d125387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163657 q = 1) : d125388 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d163657, d125388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163657, d125388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36716 (p : Pattern) (ha : d122306 p = 1) (hb : d163663 p = 1) : d125394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163658 q = 1) : d125389 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d163658, d125389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36715 q ha hb
    | true =>
      simp only [d163658, d125389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163659 q = 1) : d125390 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d163659, d125390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163659, d125390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163660 q = 1) : d125391 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d163660, d125391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163660, d125391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163661 q = 1) : d125392 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d163661, d125392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163661, d125392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163662 q = 1) : d125393 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d163662, d125393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163662, d125393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163663 q = 1) : d125394 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d163663, d125394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163663, d125394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36717 (p : Pattern) (ha : d122306 p = 1) (hb : d163669 p = 1) : d125400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163664 q = 1) : d125395 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d163664, d125395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36716 q ha hb
    | true =>
      simp only [d163664, d125395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163665 q = 1) : d125396 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d163665, d125396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163665, d125396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163666 q = 1) : d125397 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d163666, d125397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163666, d125397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163667 q = 1) : d125398 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d163667, d125398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163667, d125398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163668 q = 1) : d125399 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d163668, d125399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163668, d125399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163669 q = 1) : d125400 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d163669, d125400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163669, d125400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36718 (p : Pattern) (ha : d122306 p = 1) (hb : d163675 p = 1) : d125406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163670 q = 1) : d125401 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d163670, d125401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36717 q ha hb
    | true =>
      simp only [d163670, d125401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163671 q = 1) : d125402 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d163671, d125402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163671, d125402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163672 q = 1) : d125403 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d163672, d125403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163672, d125403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163673 q = 1) : d125404 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d163673, d125404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163673, d125404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163674 q = 1) : d125405 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d163674, d125405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163674, d125405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163675 q = 1) : d125406 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d163675, d125406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163675, d125406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36719 (p : Pattern) (ha : d122306 p = 1) (hb : d163681 p = 1) : d125412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d163676 q = 1) : d125407 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d163676, d125407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36718 q ha hb
    | true =>
      simp only [d163676, d125407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d163677 q = 1) : d125408 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d163677, d125408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163677, d125408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d163678 q = 1) : d125409 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d163678, d125409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163678, d125409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d163679 q = 1) : d125410 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d163679, d125410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163679, d125410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d163680 q = 1) : d125411 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d163680, d125411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163680, d125411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d163681 q = 1) : d125412 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d163681, d125412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163681, d125412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36720 (p : Pattern) (ha : d92414 p = 1) (hb : d123951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92394 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92403 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92322 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36407 q ha hb
    | true =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d92404 q = 1) (hb : d123947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92404, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92410 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92411 q = 1) (hb : d123948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92411, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92412 q = 1) (hb : d123949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92412, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92413 q = 1) (hb : d123950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92413, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92414 q = 1) (hb : d123951 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92414, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92414, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro36721 (p : Pattern) (ha : d92433 p = 1) (hb : d123958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92403 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92322 q = 1) (hb : d123892 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36407 q ha hb
    | true =>
      simp only [d92322, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d92404 q = 1) (hb : d123947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92404, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92410 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92411 q = 1) (hb : d123948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92411, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92412 q = 1) (hb : d123949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92412, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92413 q = 1) (hb : d123950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92413, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92419 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92423 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92425 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92329 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36409 q ha hb
    | true =>
      simp only [d92329, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d92426 q = 1) (hb : d123954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92426, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92429 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92430 q = 1) (hb : d123955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92430, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92431 q = 1) (hb : d123956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92431, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92431, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92432 q = 1) (hb : d123957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92432, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92432, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92433 q = 1) (hb : d123958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92433, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92433, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro36722 (p : Pattern) (ha : d92442 p = 1) (hb : d125190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92425 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92329 q = 1) (hb : d123899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36409 q ha hb
    | true =>
      simp only [d92329, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d92426 q = 1) (hb : d123954 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92426, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92429 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92430 q = 1) (hb : d123955 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92430, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92440 q = 1) (hb : d123956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92440, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92440, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92441 q = 1) (hb : d123957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92441, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92441, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92442 q = 1) (hb : d125190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92442, d125190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92442, d125190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36723 (p : Pattern) (ha : d92467 p = 1) (hb : d125200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92351 q = 1) (hb : d123930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92351, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36414 q ha hb
    | true =>
      simp only [d92351, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d92457 q = 1) (hb : d125196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92457, d125196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92457, d125196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92463 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92464 q = 1) (hb : d125197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92464, d125197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92464, d125197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92465 q = 1) (hb : d125198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92465, d125198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92465, d125198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92466 q = 1) (hb : d125199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92466, d125199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92466, d125199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92467 q = 1) (hb : d125200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92467, d125200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92467, d125200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36724 (p : Pattern) (ha : d92473 p = 1) (hb : d125206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92382 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92434 q = 1) (hb : d123959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92434, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36720 q ha hb
    | true =>
      simp only [d92434, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36721 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92437 q = 1) (hb : d123960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92437, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92437, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92438 q = 1) (hb : d125188 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92438, d125188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92438, d125188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92439 q = 1) (hb : d125189 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92439, d125189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92439, d125189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92443 q = 1) (hb : d125191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92443, d125191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92443, d125191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36722 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92444 q = 1) (hb : d125192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92444, d125192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92444, d125192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92445 q = 1) (hb : d125193 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92445, d125193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92445, d125193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92446 q = 1) (hb : d125194 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92446, d125194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92446, d125194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92447 q = 1) (hb : d125195 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92447, d125195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92447, d125195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92468 q = 1) (hb : d125201 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92468, d125201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92468, d125201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36723 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92469 q = 1) (hb : d125202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92469, d125202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92469, d125202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92470 q = 1) (hb : d125203 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92470, d125203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92470, d125203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92471 q = 1) (hb : d125204 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92471, d125204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92471, d125204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92472 q = 1) (hb : d125205 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92472, d125205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92472, d125205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92473 q = 1) (hb : d125206 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92473, d125206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92473, d125206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro36725 (p : Pattern) (ha : d92479 p = 1) (hb : d125212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d92363 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d92363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d92363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11594 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d92364 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d92364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d92364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d92365 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d92365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d92365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d92366 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d92366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d92366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d92367 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d92367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d92367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92474 q = 1) (hb : d125207 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92474, d125207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92474, d125207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36724 q ha hb
  have h8 (q : Pattern) (ha : d92475 q = 1) (hb : d125208 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92475, d125208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92475, d125208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92476 q = 1) (hb : d125209 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92476, d125209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92476, d125209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92477 q = 1) (hb : d125210 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92477, d125210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92477, d125210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92478 q = 1) (hb : d125211 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92478, d125211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92478, d125211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92479 q = 1) (hb : d125212 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92479, d125212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d92479, d125212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro36726 (p : Pattern) (ha : d92538 p = 1) (hb : d124086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92507 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92513 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92527 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92484 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36448 q ha hb
    | true =>
      simp only [d92484, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36441 q ha hb
  have h5 (q : Pattern) (ha : d92528 q = 1) (hb : d124082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92528, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92534 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92535 q = 1) (hb : d124083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92535, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92536 q = 1) (hb : d124084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92536, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92537 q = 1) (hb : d124085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92537, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92538 q = 1) (hb : d124086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92538, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92538, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro36727 (p : Pattern) (ha : d92558 p = 1) (hb : d124096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92507 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92513 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92484 q = 1) (hb : d124081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36448 q ha hb
    | true =>
      simp only [d92484, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36441 q ha hb
  have h4 (q : Pattern) (ha : d92528 q = 1) (hb : d124082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92528, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92535 q = 1) (hb : d124083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92535, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92536 q = 1) (hb : d124084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92536, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92537 q = 1) (hb : d124085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92537, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92543 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92550 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92493 q = 1) (hb : d124091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92493, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36450 q ha hb
    | true =>
      simp only [d92493, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36442 q ha hb
  have h13 (q : Pattern) (ha : d92551 q = 1) (hb : d124092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92551, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92554 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92555 q = 1) (hb : d124093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92555, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92556 q = 1) (hb : d124094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92556, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92556, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92557 q = 1) (hb : d124095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92557, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92557, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92558 q = 1) (hb : d124096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92558, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92558, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro36728 (p : Pattern) (ha : d92572 p = 1) (hb : d125215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92550 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92493 q = 1) (hb : d124091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92493, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36450 q ha hb
    | true =>
      simp only [d92493, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36442 q ha hb
  have h3 (q : Pattern) (ha : d92551 q = 1) (hb : d124092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92551, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92554 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92555 q = 1) (hb : d124093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92555, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92570 q = 1) (hb : d124094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92570, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92570, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92571 q = 1) (hb : d124095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92571, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92571, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92572 q = 1) (hb : d125215 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92572, d125215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92572, d125215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36729 (p : Pattern) (ha : d92595 p = 1) (hb : d124210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92450 q = 1) (hb : d124039 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92450, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36434 q ha hb
    | true =>
      simp only [d92450, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92451 q = 1) (hb : d124040 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92451, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92451, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52388 q = 1) (hb : d124205 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52388, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36445 q ha hb
    | true =>
      simp only [d52388, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52389 q = 1) (hb : d124206 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52389, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52389, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92592 q = 1) (hb : d124207 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92592, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92592, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92593 q = 1) (hb : d124208 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92593, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92593, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92594 q = 1) (hb : d124209 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92594, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92594, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92595 q = 1) (hb : d124210 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92595, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92595, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36730 (p : Pattern) (ha : d92607 p = 1) (hb : d125226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92591 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92596 q = 1) (hb : d125221 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92596, d125221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36729 q ha hb
    | true =>
      simp only [d92596, d125221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36446 q ha hb
  have h3 (q : Pattern) (ha : d92597 q = 1) (hb : d125222 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92597, d125222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92597, d125222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92604 q = 1) (hb : d125223 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92604, d125223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92604, d125223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92605 q = 1) (hb : d125224 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92605, d125224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92605, d125224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92606 q = 1) (hb : d125225 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92606, d125225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92606, d125225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92607 q = 1) (hb : d125226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92607, d125226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92607, d125226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36731 (p : Pattern) (ha : d92613 p = 1) (hb : d125232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92501 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92559 q = 1) (hb : d124097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92559, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36726 q ha hb
    | true =>
      simp only [d92559, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36727 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92566 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92567 q = 1) (hb : d124098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92567, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92567, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92568 q = 1) (hb : d125213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92568, d125213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92568, d125213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92569 q = 1) (hb : d125214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92569, d125214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92569, d125214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92573 q = 1) (hb : d125216 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92573, d125216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92573, d125216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36728 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92574 q = 1) (hb : d125217 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92574, d125217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92574, d125217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92575 q = 1) (hb : d125218 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92575, d125218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92575, d125218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92576 q = 1) (hb : d125219 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92576, d125219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92576, d125219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92577 q = 1) (hb : d125220 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92577, d125220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92577, d125220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92608 q = 1) (hb : d125227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92608, d125227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92608, d125227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36730 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92609 q = 1) (hb : d125228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92609, d125228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92609, d125228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92610 q = 1) (hb : d125229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92610, d125229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92610, d125229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92611 q = 1) (hb : d125230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92611, d125230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92611, d125230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92612 q = 1) (hb : d125231 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92612, d125231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92612, d125231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92613 q = 1) (hb : d125232 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92613, d125232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92613, d125232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro36732 (p : Pattern) (ha : d92619 p = 1) (hb : d125238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92614 q = 1) (hb : d125233 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92614, d125233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92614, d125233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36731 q ha hb
  have h2 (q : Pattern) (ha : d92615 q = 1) (hb : d125234 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92615, d125234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92615, d125234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92616 q = 1) (hb : d125235 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92616, d125235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92616, d125235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92617 q = 1) (hb : d125236 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92617, d125236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92617, d125236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92618 q = 1) (hb : d125237 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92618, d125237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92618, d125237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92619 q = 1) (hb : d125238 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92619, d125238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92619, d125238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36733 (p : Pattern) (ha : d92683 p = 1) (hb : d124272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92672 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92629 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36494 q ha hb
    | true =>
      simp only [d92629, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36484 q ha hb
  have h5 (q : Pattern) (ha : d92673 q = 1) (hb : d124268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92673, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92679 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92680 q = 1) (hb : d124269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92680, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92681 q = 1) (hb : d124270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92681, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92682 q = 1) (hb : d124271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92682, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92683 q = 1) (hb : d124272 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92683, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92683, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro36734 (p : Pattern) (ha : d92703 p = 1) (hb : d124282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92629 q = 1) (hb : d124267 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92629, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36494 q ha hb
    | true =>
      simp only [d92629, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36484 q ha hb
  have h4 (q : Pattern) (ha : d92673 q = 1) (hb : d124268 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92673, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92673, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92679 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92680 q = 1) (hb : d124269 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92680, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92680, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92681 q = 1) (hb : d124270 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92681, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92681, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92682 q = 1) (hb : d124271 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92682, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92682, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92688 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92692 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92695 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92638 q = 1) (hb : d124277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92638, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36496 q ha hb
    | true =>
      simp only [d92638, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36485 q ha hb
  have h13 (q : Pattern) (ha : d92696 q = 1) (hb : d124278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92696, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92699 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92700 q = 1) (hb : d124279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92700, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92701 q = 1) (hb : d124280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92701, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92701, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92702 q = 1) (hb : d124281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92702, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92702, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92703 q = 1) (hb : d124282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92703, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92703, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro36735 (p : Pattern) (ha : d92717 p = 1) (hb : d125242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92695 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92638 q = 1) (hb : d124277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92638, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36496 q ha hb
    | true =>
      simp only [d92638, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36485 q ha hb
  have h3 (q : Pattern) (ha : d92696 q = 1) (hb : d124278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92696, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92696, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92699 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92700 q = 1) (hb : d124279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92700, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92700, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92715 q = 1) (hb : d124280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92715, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92715, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92716 q = 1) (hb : d124281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92716, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92716, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92717 q = 1) (hb : d125242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92717, d125242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92717, d125242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36736 (p : Pattern) (ha : d92744 p = 1) (hb : d124404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92739 q = 1) (hb : d124391 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92739, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36525 q ha hb
    | true =>
      simp only [d92739, d124391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92740 q = 1) (hb : d124392 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92740, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92740, d124392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52625 q = 1) (hb : d124399 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52625, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36489 q ha hb
    | true =>
      simp only [d52625, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52626 q = 1) (hb : d124400 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52626, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52626, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92741 q = 1) (hb : d124401 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92741, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92741, d124401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92742 q = 1) (hb : d124402 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92742, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92742, d124402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92743 q = 1) (hb : d124403 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92743, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92743, d124403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92744 q = 1) (hb : d124404 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92744, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92744, d124404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36737 (p : Pattern) (ha : d92756 p = 1) (hb : d125253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92736 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92745 q = 1) (hb : d125248 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92745, d125248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36736 q ha hb
    | true =>
      simp only [d92745, d125248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36490 q ha hb
  have h3 (q : Pattern) (ha : d92746 q = 1) (hb : d125249 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92746, d125249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92746, d125249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92752 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92753 q = 1) (hb : d125250 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92753, d125250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92753, d125250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92754 q = 1) (hb : d125251 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92754, d125251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92754, d125251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92755 q = 1) (hb : d125252 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92755, d125252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92755, d125252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92756 q = 1) (hb : d125253 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92756, d125253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92756, d125253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36738 (p : Pattern) (ha : d92762 p = 1) (hb : d125259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92646 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92704 q = 1) (hb : d124283 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92704, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36733 q ha hb
    | true =>
      simp only [d92704, d124283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36734 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92711 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92712 q = 1) (hb : d124284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92712, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92712, d124284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92713 q = 1) (hb : d125240 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92713, d125240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92713, d125240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92714 q = 1) (hb : d125241 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92714, d125241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92714, d125241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92718 q = 1) (hb : d125243 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92718, d125243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92718, d125243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36735 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92719 q = 1) (hb : d125244 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92719, d125244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92719, d125244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92720 q = 1) (hb : d125245 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92720, d125245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92720, d125245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92721 q = 1) (hb : d125246 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92721, d125246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92721, d125246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92722 q = 1) (hb : d125247 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92722, d125247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92722, d125247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92757 q = 1) (hb : d125254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92757, d125254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92757, d125254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36737 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92758 q = 1) (hb : d125255 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92758, d125255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92758, d125255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92759 q = 1) (hb : d125256 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92759, d125256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92759, d125256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92760 q = 1) (hb : d125257 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92760, d125257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92760, d125257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92761 q = 1) (hb : d125258 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92761, d125258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92761, d125258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92762 q = 1) (hb : d125259 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92762, d125259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92762, d125259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro36739 (p : Pattern) (ha : d92768 p = 1) (hb : d125265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92763 q = 1) (hb : d125260 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92763, d125260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92763, d125260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36738 q ha hb
  have h2 (q : Pattern) (ha : d92764 q = 1) (hb : d125261 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92764, d125261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92764, d125261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92765 q = 1) (hb : d125262 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92765, d125262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92765, d125262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92766 q = 1) (hb : d125263 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92766, d125263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92766, d125263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92767 q = 1) (hb : d125264 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92767, d125264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92767, d125264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92768 q = 1) (hb : d125265 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92768, d125265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92768, d125265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36740 (p : Pattern) (ha : d92833 p = 1) (hb : d124473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92802 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92822 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92779 q = 1) (hb : d124468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36542 q ha hb
    | true =>
      simp only [d92779, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36532 q ha hb
  have h5 (q : Pattern) (ha : d92823 q = 1) (hb : d124469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92823, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92829 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92830 q = 1) (hb : d124470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92830, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92831 q = 1) (hb : d124471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92831, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92832 q = 1) (hb : d124472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92832, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92833 q = 1) (hb : d124473 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92833, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92833, d124473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro36741 (p : Pattern) (ha : d92853 p = 1) (hb : d124483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92808 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92822 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92779 q = 1) (hb : d124468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92779, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36542 q ha hb
    | true =>
      simp only [d92779, d124468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36532 q ha hb
  have h4 (q : Pattern) (ha : d92823 q = 1) (hb : d124469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92823, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92823, d124469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92829 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92830 q = 1) (hb : d124470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92830, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92830, d124470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92831 q = 1) (hb : d124471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92831, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92831, d124471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92832 q = 1) (hb : d124472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92832, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92832, d124472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92838 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92842 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92845 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92788 q = 1) (hb : d124478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92788, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36544 q ha hb
    | true =>
      simp only [d92788, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36533 q ha hb
  have h13 (q : Pattern) (ha : d92846 q = 1) (hb : d124479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92846, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d92849 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92850 q = 1) (hb : d124480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92850, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92851 q = 1) (hb : d124481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92851, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d92851, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92852 q = 1) (hb : d124482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92852, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d92852, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92853 q = 1) (hb : d124483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92853, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92853, d124483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro36742 (p : Pattern) (ha : d92867 p = 1) (hb : d125270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92788 q = 1) (hb : d124478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92788, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36544 q ha hb
    | true =>
      simp only [d92788, d124478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36533 q ha hb
  have h3 (q : Pattern) (ha : d92846 q = 1) (hb : d124479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92846, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92846, d124479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92849 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92850 q = 1) (hb : d124480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92850, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92850, d124480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92865 q = 1) (hb : d124481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92865, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92865, d124481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92866 q = 1) (hb : d124482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92866, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92866, d124482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92867 q = 1) (hb : d125270 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92867, d125270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92867, d125270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36743 (p : Pattern) (ha : d92894 p = 1) (hb : d125279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92889 q = 1) (hb : d124638 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92889, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36573 q ha hb
    | true =>
      simp only [d92889, d124638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92890 q = 1) (hb : d124639 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92890, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92890, d124639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52919 q = 1) (hb : d124628 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d52919, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36537 q ha hb
    | true =>
      simp only [d52919, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d52920 q = 1) (hb : d124629 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d52920, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52920, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92891 q = 1) (hb : d125276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92891, d125276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92891, d125276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92892 q = 1) (hb : d125277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92892, d125277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92892, d125277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92893 q = 1) (hb : d125278 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92893, d125278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92893, d125278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92894 q = 1) (hb : d125279 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92894, d125279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92894, d125279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36744 (p : Pattern) (ha : d92906 p = 1) (hb : d125285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92886 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92895 q = 1) (hb : d125280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92895, d125280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36743 q ha hb
    | true =>
      simp only [d92895, d125280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36538 q ha hb
  have h3 (q : Pattern) (ha : d92896 q = 1) (hb : d125281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92896, d125281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92896, d125281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92903 q = 1) (hb : d125282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92903, d125282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92903, d125282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92904 q = 1) (hb : d125283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92904, d125283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92904, d125283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92905 q = 1) (hb : d125284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92905, d125284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92905, d125284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92906 q = 1) (hb : d125285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92906, d125285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92906, d125285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36745 (p : Pattern) (ha : d92912 p = 1) (hb : d125291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92796 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92854 q = 1) (hb : d124484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92854, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36740 q ha hb
    | true =>
      simp only [d92854, d124484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36741 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92861 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92862 q = 1) (hb : d124485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92862, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92862, d124485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d92863 q = 1) (hb : d125268 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92863, d125268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92863, d125268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92864 q = 1) (hb : d125269 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92864, d125269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92864, d125269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92868 q = 1) (hb : d125271 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92868, d125271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92868, d125271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36742 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d92869 q = 1) (hb : d125272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92869, d125272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92869, d125272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92870 q = 1) (hb : d125273 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92870, d125273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92870, d125273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d92871 q = 1) (hb : d125274 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92871, d125274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92871, d125274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d92872 q = 1) (hb : d125275 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92872, d125275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92872, d125275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92907 q = 1) (hb : d125286 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92907, d125286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92907, d125286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36744 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d92908 q = 1) (hb : d125287 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92908, d125287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92908, d125287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d92909 q = 1) (hb : d125288 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92909, d125288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92909, d125288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d92910 q = 1) (hb : d125289 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92910, d125289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92910, d125289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d92911 q = 1) (hb : d125290 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92911, d125290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92911, d125290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d92912 q = 1) (hb : d125291 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92912, d125291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92912, d125291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro36746 (p : Pattern) (ha : d92918 p = 1) (hb : d125297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92913 q = 1) (hb : d125292 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92913, d125292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92913, d125292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36745 q ha hb
  have h2 (q : Pattern) (ha : d92914 q = 1) (hb : d125293 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92914, d125293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92914, d125293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92915 q = 1) (hb : d125294 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92915, d125294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92915, d125294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92916 q = 1) (hb : d125295 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92916, d125295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92916, d125295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92917 q = 1) (hb : d125296 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92917, d125296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92917, d125296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92918 q = 1) (hb : d125297 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92918, d125297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92918, d125297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36747 (p : Pattern) (ha : d92984 p = 1) (hb : d124707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92953 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92959 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92973 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92930 q = 1) (hb : d124702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36590 q ha hb
    | true =>
      simp only [d92930, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36580 q ha hb
  have h5 (q : Pattern) (ha : d92974 q = 1) (hb : d124703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92974, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d92980 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d92981 q = 1) (hb : d124704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92981, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d92982 q = 1) (hb : d124705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92982, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92983 q = 1) (hb : d124706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92983, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92984 q = 1) (hb : d124707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92984, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92984, d124707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro36748 (p : Pattern) (ha : d93004 p = 1) (hb : d124717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92953 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92973 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92930 q = 1) (hb : d124702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92930, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36590 q ha hb
    | true =>
      simp only [d92930, d124702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36580 q ha hb
  have h4 (q : Pattern) (ha : d92974 q = 1) (hb : d124703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92974, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d92974, d124703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d92980 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d92981 q = 1) (hb : d124704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92981, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92981, d124704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92982 q = 1) (hb : d124705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92982, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92982, d124705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92983 q = 1) (hb : d124706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92983, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92983, d124706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92989 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d92993 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d92996 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d92939 q = 1) (hb : d124712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92939, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36592 q ha hb
    | true =>
      simp only [d92939, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36581 q ha hb
  have h13 (q : Pattern) (ha : d92997 q = 1) (hb : d124713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d92997, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d93000 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d93001 q = 1) (hb : d124714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d93001, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d93002 q = 1) (hb : d124715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93002, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d93002, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d93003 q = 1) (hb : d124716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93003, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d93003, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d93004 q = 1) (hb : d124717 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93004, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d93004, d124717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro36749 (p : Pattern) (ha : d93018 p = 1) (hb : d125303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92996 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92939 q = 1) (hb : d124712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92939, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36592 q ha hb
    | true =>
      simp only [d92939, d124712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36581 q ha hb
  have h3 (q : Pattern) (ha : d92997 q = 1) (hb : d124713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92997, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d92997, d124713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d93000 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d93001 q = 1) (hb : d124714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d93001, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d93001, d124714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d93016 q = 1) (hb : d124715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d93016, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93016, d124715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d93017 q = 1) (hb : d124716 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d93017, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93017, d124716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d93018 q = 1) (hb : d125303 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d93018, d125303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d93018, d125303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
