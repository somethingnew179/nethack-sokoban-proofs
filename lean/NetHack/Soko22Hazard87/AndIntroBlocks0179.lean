import NetHack.Soko22Hazard87.AndIntroBlocks0178
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro44750 (p : Pattern) (ha : d181811 p = 1) (hb : d188699 p = 1) : d192504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181811 q = 1) (hb : d188694 q = 1) : d192499 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d188694, d192499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44749 q ha hb
    | true =>
      simp only [d188694, d192499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d181811 q = 1) (hb : d188695 q = 1) : d192500 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d188695, d192500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188695, d192500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d181811 q = 1) (hb : d188696 q = 1) : d192501 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d188696, d192501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188696, d192501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d181811 q = 1) (hb : d188697 q = 1) : d192502 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d188697, d192502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188697, d192502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d181811 q = 1) (hb : d188698 q = 1) : d192503 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d188698, d192503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188698, d192503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d181811 q = 1) (hb : d188699 q = 1) : d192504 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d188699, d192504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188699, d192504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44751 (p : Pattern) (ha : d181811 p = 1) (hb : d188705 p = 1) : d192510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181811 q = 1) (hb : d188700 q = 1) : d192505 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d188700, d192505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44750 q ha hb
    | true =>
      simp only [d188700, d192505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d181811 q = 1) (hb : d188701 q = 1) : d192506 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d188701, d192506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188701, d192506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d181811 q = 1) (hb : d188702 q = 1) : d192507 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d188702, d192507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188702, d192507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d181811 q = 1) (hb : d188703 q = 1) : d192508 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d188703, d192508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188703, d192508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d181811 q = 1) (hb : d188704 q = 1) : d192509 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d188704, d192509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188704, d192509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d181811 q = 1) (hb : d188705 q = 1) : d192510 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d188705, d192510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188705, d192510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44752 (p : Pattern) (ha : d181811 p = 1) (hb : d188711 p = 1) : d192516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181811 q = 1) (hb : d188706 q = 1) : d192511 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d188706, d192511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44751 q ha hb
    | true =>
      simp only [d188706, d192511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d181811 q = 1) (hb : d188707 q = 1) : d192512 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d188707, d192512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188707, d192512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d181811 q = 1) (hb : d188708 q = 1) : d192513 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d188708, d192513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188708, d192513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d181811 q = 1) (hb : d188709 q = 1) : d192514 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d188709, d192514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188709, d192514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d181811 q = 1) (hb : d188710 q = 1) : d192515 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d188710, d192515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188710, d192515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d181811 q = 1) (hb : d188711 q = 1) : d192516 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d188711, d192516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188711, d192516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44753 (p : Pattern) (ha : d181811 p = 1) (hb : d188717 p = 1) : d192522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181811 q = 1) (hb : d188712 q = 1) : d192517 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d188712, d192517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44752 q ha hb
    | true =>
      simp only [d188712, d192517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d181811 q = 1) (hb : d188713 q = 1) : d192518 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d188713, d192518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188713, d192518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d181811 q = 1) (hb : d188714 q = 1) : d192519 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d188714, d192519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188714, d192519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d181811 q = 1) (hb : d188715 q = 1) : d192520 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d188715, d192520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188715, d192520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d181811 q = 1) (hb : d188716 q = 1) : d192521 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d188716, d192521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188716, d192521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d181811 q = 1) (hb : d188717 q = 1) : d192522 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d188717, d192522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188717, d192522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44754 (p : Pattern) (ha : d181811 p = 1) (hb : d188723 p = 1) : d192528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d181811 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d181811 q = 1) (hb : d188718 q = 1) : d192523 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d188718, d192523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44753 q ha hb
    | true =>
      simp only [d188718, d192523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d181811 q = 1) (hb : d188719 q = 1) : d192524 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d188719, d192524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d188719, d192524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d181811 q = 1) (hb : d188720 q = 1) : d192525 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d188720, d192525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d188720, d192525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d181811 q = 1) (hb : d188721 q = 1) : d192526 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d188721, d192526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d188721, d192526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d181811 q = 1) (hb : d188722 q = 1) : d192527 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d188722, d192527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d188722, d192527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d181811 q = 1) (hb : d188723 q = 1) : d192528 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d188723, d192528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d188723, d192528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44755 (p : Pattern) (ha : d191326 p = 1) (hb : d191904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d191321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d191294 q = 1) (hb : d191832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191294, d191832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44612 q ha hb
    | true =>
      simp only [d191294, d191832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d191322 q = 1) (hb : d191900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191322, d191900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191322, d191900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d191295 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d191323 q = 1) (hb : d191901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191323, d191901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191323, d191901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d191324 q = 1) (hb : d191902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191324, d191902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191324, d191902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d191325 q = 1) (hb : d191903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191325, d191903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191325, d191903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d191326 q = 1) (hb : d191904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191326, d191904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191326, d191904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44756 (p : Pattern) (ha : d191332 p = 1) (hb : d192334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191327 q = 1) (hb : d191905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191327, d191905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191327, d191905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44755 q ha hb
  have h2 (q : Pattern) (ha : d191328 q = 1) (hb : d192330 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d191328, d192330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191328, d192330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d191329 q = 1) (hb : d192331 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d191329, d192331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191329, d192331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191330 q = 1) (hb : d192332 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d191330, d192332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191330, d192332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191331 q = 1) (hb : d192333 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d191331, d192333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191331, d192333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191332 q = 1) (hb : d192334 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d191332, d192334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191332, d192334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44757 (p : Pattern) (ha : d191360 p = 1) (hb : d192344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d191349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d191321 q = 1) (hb : d191859 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191321, d191859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44617 q ha hb
    | true =>
      simp only [d191321, d191859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44612 q ha hb
  have h3 (q : Pattern) (ha : d191350 q = 1) (hb : d192340 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191350, d192340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191350, d192340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d191356 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d191357 q = 1) (hb : d192341 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191357, d192341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191357, d192341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d191358 q = 1) (hb : d192342 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191358, d192342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191358, d192342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d191359 q = 1) (hb : d192343 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191359, d192343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191359, d192343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d191360 q = 1) (hb : d192344 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191360, d192344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191360, d192344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44758 (p : Pattern) (ha : d191372 p = 1) (hb : d192350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191361 q = 1) (hb : d192345 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191361, d192345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191361, d192345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44757 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191367 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d191368 q = 1) (hb : d192346 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d191368, d192346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191368, d192346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d191369 q = 1) (hb : d192347 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d191369, d192347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191369, d192347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191370 q = 1) (hb : d192348 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d191370, d192348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191370, d192348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191371 q = 1) (hb : d192349 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d191371, d192349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191371, d192349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d191372 q = 1) (hb : d192350 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d191372, d192350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191372, d192350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44759 (p : Pattern) (ha : d191378 p = 1) (hb : d192356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d191309 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d191333 q = 1) (hb : d192335 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d191333, d192335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191333, d192335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44756 q ha hb
  have h3 (q : Pattern) (ha : d191334 q = 1) (hb : d192336 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d191334, d192336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191334, d192336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d191335 q = 1) (hb : d192337 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d191335, d192337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191335, d192337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d191336 q = 1) (hb : d192338 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d191336, d192338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191336, d192338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191337 q = 1) (hb : d192339 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d191337, d192339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191337, d192339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d191373 q = 1) (hb : d192351 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d191373, d192351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191373, d192351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44758 q ha hb
  have h8 (q : Pattern) (ha : d191374 q = 1) (hb : d192352 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d191374, d192352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191374, d192352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d191375 q = 1) (hb : d192353 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d191375, d192353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191375, d192353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d191376 q = 1) (hb : d192354 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d191376, d192354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191376, d192354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d191377 q = 1) (hb : d192355 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d191377, d192355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191377, d192355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d191378 q = 1) (hb : d192356 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d191378, d192356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d191378, d192356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro44760 (p : Pattern) (ha : d191421 p = 1) (hb : d192362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d191405 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d191410 q = 1) (hb : d192357 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191410, d192357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44634 q ha hb
    | true =>
      simp only [d191410, d192357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44637 q ha hb
  have h3 (q : Pattern) (ha : d191411 q = 1) (hb : d192358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191411, d192358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191411, d192358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d191417 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d191418 q = 1) (hb : d192359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191418, d192359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191418, d192359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d191419 q = 1) (hb : d192360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191419, d192360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191419, d192360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d191420 q = 1) (hb : d192361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191420, d192361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191420, d192361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d191421 q = 1) (hb : d192362 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191421, d192362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191421, d192362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44761 (p : Pattern) (ha : d191434 p = 1) (hb : d192368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191422 q = 1) (hb : d192363 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191422, d192363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191422, d192363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44760 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191429 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d191430 q = 1) (hb : d192364 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d191430, d192364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191430, d192364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d191431 q = 1) (hb : d192365 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d191431, d192365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191431, d192365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191432 q = 1) (hb : d192366 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d191432, d192366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191432, d192366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191433 q = 1) (hb : d192367 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d191433, d192367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191433, d192367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d191434 q = 1) (hb : d192368 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d191434, d192368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191434, d192368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44762 (p : Pattern) (ha : d191440 p = 1) (hb : d192374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191435 q = 1) (hb : d192369 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d191435, d192369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191435, d192369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44761 q ha hb
  have h2 (q : Pattern) (ha : d191436 q = 1) (hb : d192370 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d191436, d192370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191436, d192370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d191437 q = 1) (hb : d192371 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d191437, d192371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191437, d192371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d191438 q = 1) (hb : d192372 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d191438, d192372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191438, d192372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d191439 q = 1) (hb : d192373 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d191439, d192373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191439, d192373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191440 q = 1) (hb : d192374 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d191440, d192374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191440, d192374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44763 (p : Pattern) (ha : d191489 p = 1) (hb : d192381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d191473 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d191478 q = 1) (hb : d192376 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191478, d192376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44650 q ha hb
    | true =>
      simp only [d191478, d192376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44653 q ha hb
  have h3 (q : Pattern) (ha : d191479 q = 1) (hb : d192377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191479, d192377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191479, d192377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d191485 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d191486 q = 1) (hb : d192378 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191486, d192378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191486, d192378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d191487 q = 1) (hb : d192379 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191487, d192379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191487, d192379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d191488 q = 1) (hb : d192380 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191488, d192380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191488, d192380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d191489 q = 1) (hb : d192381 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191489, d192381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191489, d192381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44764 (p : Pattern) (ha : d191502 p = 1) (hb : d192387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191490 q = 1) (hb : d192382 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191490, d192382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191490, d192382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44763 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191497 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d191498 q = 1) (hb : d192383 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d191498, d192383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191498, d192383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d191499 q = 1) (hb : d192384 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d191499, d192384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191499, d192384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191500 q = 1) (hb : d192385 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d191500, d192385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191500, d192385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191501 q = 1) (hb : d192386 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d191501, d192386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191501, d192386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d191502 q = 1) (hb : d192387 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d191502, d192387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191502, d192387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44765 (p : Pattern) (ha : d191508 p = 1) (hb : d192393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191503 q = 1) (hb : d192388 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d191503, d192388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191503, d192388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44764 q ha hb
  have h2 (q : Pattern) (ha : d191504 q = 1) (hb : d192389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d191504, d192389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191504, d192389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d191505 q = 1) (hb : d192390 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d191505, d192390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191505, d192390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d191506 q = 1) (hb : d192391 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d191506, d192391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191506, d192391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d191507 q = 1) (hb : d192392 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d191507, d192392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191507, d192392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191508 q = 1) (hb : d192393 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d191508, d192393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191508, d192393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44766 (p : Pattern) (ha : d191547 p = 1) (hb : d192397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d174945 q = 1) (hb : d183886 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174945, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44658 q ha hb
    | true =>
      simp only [d174945, d183886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44660 q ha hb
  have h2 (q : Pattern) (ha : d174946 q = 1) (hb : d183887 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174946, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174946, d183887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d174947 q = 1) (hb : d183888 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174947, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174947, d183888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d174953 q = 1) (hb : d183896 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174953, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44660 q ha hb
    | true =>
      simp only [d174953, d183896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44661 q ha hb
  have h5 (q : Pattern) (ha : d174954 q = 1) (hb : d183897 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174954, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174954, d183897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d174955 q = 1) (hb : d183898 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174955, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174955, d183898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d174956 q = 1) (hb : d183899 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174956, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d174956, d183899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d174972 q = 1) (hb : d183915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d174972, d183915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44660 q ha hb
    | true =>
      simp only [d174972, d183915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44665 q ha hb
  have h9 (q : Pattern) (ha : d174973 q = 1) (hb : d183916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d174973, d183916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174973, d183916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d174974 q = 1) (hb : d183917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d174974, d183917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d174974, d183917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d174975 q = 1) (hb : d183918 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d174975, d183918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d174975, d183918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d174985 q = 1) (hb : d184337 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d174985, d184337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d174985, d184337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d191516 q = 1) (hb : d192052 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191516, d192052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191516, d192052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d191517 q = 1) (hb : d192053 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191517, d192053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191517, d192053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d191518 q = 1) (hb : d192054 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191518, d192054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191518, d192054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d191519 q = 1) (hb : d192055 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191519, d192055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191519, d192055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d191520 q = 1) (hb : d192056 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191520, d192056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d191520, d192056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d191534 q = 1) (hb : d192070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191534, d192070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d191534, d192070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d191535 q = 1) (hb : d192071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191535, d192071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191535, d192071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d191536 q = 1) (hb : d192072 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191536, d192072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d191536, d192072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d191546 q = 1) (hb : d192396 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191546, d192396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d191546, d192396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d191547 q = 1) (hb : d192397 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191547, d192397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d191547, d192397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro44767 (p : Pattern) (ha : d191553 p = 1) (hb : d192403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191548 q = 1) (hb : d192398 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191548, d192398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44766 q ha hb
    | true =>
      simp only [d191548, d192398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d191549 q = 1) (hb : d192399 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191549, d192399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191549, d192399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d191539 q = 1) (hb : d192075 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191539, d192075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44666 q ha hb
    | true =>
      simp only [d191539, d192075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191540 q = 1) (hb : d192076 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191540, d192076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191540, d192076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d191550 q = 1) (hb : d192400 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191550, d192400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191550, d192400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191551 q = 1) (hb : d192401 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191551, d192401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191551, d192401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d191552 q = 1) (hb : d192402 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191552, d192402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d191552, d192402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d191553 q = 1) (hb : d192403 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191553, d192403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d191553, d192403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro44768 (p : Pattern) (ha : d191576 p = 1) (hb : d192409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d191545 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d191558 q = 1) (hb : d192404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191558, d192404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44767 q ha hb
    | true =>
      simp only [d191558, d192404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44672 q ha hb
  have h3 (q : Pattern) (ha : d191559 q = 1) (hb : d192405 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191559, d192405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191559, d192405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d191572 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d191573 q = 1) (hb : d192406 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191573, d192406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191573, d192406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d191574 q = 1) (hb : d192407 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191574, d192407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191574, d192407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d191575 q = 1) (hb : d192408 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191575, d192408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191575, d192408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d191576 q = 1) (hb : d192409 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191576, d192409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191576, d192409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44769 (p : Pattern) (ha : d191589 p = 1) (hb : d192415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191577 q = 1) (hb : d192410 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191577, d192410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191577, d192410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44768 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191584 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d191585 q = 1) (hb : d192411 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d191585, d192411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191585, d192411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d191586 q = 1) (hb : d192412 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d191586, d192412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191586, d192412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191587 q = 1) (hb : d192413 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d191587, d192413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191587, d192413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191588 q = 1) (hb : d192414 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d191588, d192414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191588, d192414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d191589 q = 1) (hb : d192415 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d191589, d192415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191589, d192415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44770 (p : Pattern) (ha : d191595 p = 1) (hb : d192421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191590 q = 1) (hb : d192416 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d191590, d192416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191590, d192416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44769 q ha hb
  have h2 (q : Pattern) (ha : d191591 q = 1) (hb : d192417 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d191591, d192417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191591, d192417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d191592 q = 1) (hb : d192418 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d191592, d192418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191592, d192418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d191593 q = 1) (hb : d192419 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d191593, d192419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191593, d192419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d191594 q = 1) (hb : d192420 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d191594, d192420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191594, d192420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191595 q = 1) (hb : d192421 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d191595, d192421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191595, d192421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44771 (p : Pattern) (ha : d191635 p = 1) (hb : d192426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175068 q = 1) (hb : d184012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d175068, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44677 q ha hb
    | true =>
      simp only [d175068, d184012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44679 q ha hb
  have h2 (q : Pattern) (ha : d175069 q = 1) (hb : d184013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d175069, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175069, d184013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175070 q = 1) (hb : d184014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d175070, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175070, d184014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175076 q = 1) (hb : d184022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d175076, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44679 q ha hb
    | true =>
      simp only [d175076, d184022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44680 q ha hb
  have h5 (q : Pattern) (ha : d175077 q = 1) (hb : d184023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d175077, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175077, d184023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175078 q = 1) (hb : d184024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d175078, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175078, d184024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d175079 q = 1) (hb : d184025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d175079, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175079, d184025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d175096 q = 1) (hb : d184043 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d175096, d184043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44679 q ha hb
    | true =>
      simp only [d175096, d184043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44684 q ha hb
  have h9 (q : Pattern) (ha : d175097 q = 1) (hb : d184044 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d175097, d184044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175097, d184044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d175098 q = 1) (hb : d184045 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d175098, d184045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175098, d184045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d175099 q = 1) (hb : d184046 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d175099, d184046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d175099, d184046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d175109 q = 1) (hb : d184366 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d175109, d184366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d175109, d184366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d191604 q = 1) (hb : d192131 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191604, d192131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191604, d192131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d191605 q = 1) (hb : d192132 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191605, d192132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191605, d192132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d191606 q = 1) (hb : d192133 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191606, d192133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191606, d192133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d191607 q = 1) (hb : d192134 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191607, d192134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191607, d192134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d191608 q = 1) (hb : d192135 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191608, d192135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d191608, d192135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d191622 q = 1) (hb : d192149 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191622, d192149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d191622, d192149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d191623 q = 1) (hb : d192150 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191623, d192150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191623, d192150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d191624 q = 1) (hb : d192151 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191624, d192151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d191624, d192151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d191634 q = 1) (hb : d192425 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191634, d192425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d191634, d192425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d191635 q = 1) (hb : d192426 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191635, d192426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d191635, d192426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro44772 (p : Pattern) (ha : d191641 p = 1) (hb : d192432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191636 q = 1) (hb : d192427 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191636, d192427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44771 q ha hb
    | true =>
      simp only [d191636, d192427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d191637 q = 1) (hb : d192428 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191637, d192428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191637, d192428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d191627 q = 1) (hb : d192154 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191627, d192154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44685 q ha hb
    | true =>
      simp only [d191627, d192154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191628 q = 1) (hb : d192155 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191628, d192155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191628, d192155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d191638 q = 1) (hb : d192429 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191638, d192429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191638, d192429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191639 q = 1) (hb : d192430 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191639, d192430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191639, d192430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d191640 q = 1) (hb : d192431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191640, d192431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d191640, d192431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d191641 q = 1) (hb : d192432 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191641, d192432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d191641, d192432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro44773 (p : Pattern) (ha : d191664 p = 1) (hb : d192438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d191633 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d191646 q = 1) (hb : d192433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191646, d192433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44772 q ha hb
    | true =>
      simp only [d191646, d192433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44691 q ha hb
  have h3 (q : Pattern) (ha : d191647 q = 1) (hb : d192434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191647, d192434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191647, d192434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d191660 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d191661 q = 1) (hb : d192435 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191661, d192435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191661, d192435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d191662 q = 1) (hb : d192436 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191662, d192436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191662, d192436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d191663 q = 1) (hb : d192437 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191663, d192437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191663, d192437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d191664 q = 1) (hb : d192438 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191664, d192438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191664, d192438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44774 (p : Pattern) (ha : d191677 p = 1) (hb : d192444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191665 q = 1) (hb : d192439 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191665, d192439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191665, d192439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44773 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d191673 q = 1) (hb : d192440 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d191673, d192440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191673, d192440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d191674 q = 1) (hb : d192441 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d191674, d192441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191674, d192441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191675 q = 1) (hb : d192442 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d191675, d192442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191675, d192442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191676 q = 1) (hb : d192443 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d191676, d192443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191676, d192443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d191677 q = 1) (hb : d192444 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d191677, d192444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191677, d192444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44775 (p : Pattern) (ha : d191683 p = 1) (hb : d192450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191678 q = 1) (hb : d192445 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d191678, d192445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191678, d192445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44774 q ha hb
  have h2 (q : Pattern) (ha : d191679 q = 1) (hb : d192446 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d191679, d192446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191679, d192446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d191680 q = 1) (hb : d192447 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d191680, d192447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191680, d192447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d191681 q = 1) (hb : d192448 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d191681, d192448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191681, d192448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d191682 q = 1) (hb : d192449 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d191682, d192449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191682, d192449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191683 q = 1) (hb : d192450 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d191683, d192450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191683, d192450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44776 (p : Pattern) (ha : d191724 p = 1) (hb : d192456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d175190 q = 1) (hb : d184136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d175190, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44696 q ha hb
    | true =>
      simp only [d175190, d184136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44698 q ha hb
  have h2 (q : Pattern) (ha : d175191 q = 1) (hb : d184137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d175191, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175191, d184137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d175192 q = 1) (hb : d184138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d175192, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175192, d184138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d175198 q = 1) (hb : d184146 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d175198, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44698 q ha hb
    | true =>
      simp only [d175198, d184146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44699 q ha hb
  have h5 (q : Pattern) (ha : d175199 q = 1) (hb : d184147 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d175199, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175199, d184147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d175200 q = 1) (hb : d184148 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d175200, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175200, d184148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d175201 q = 1) (hb : d184149 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d175201, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d175201, d184149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d175218 q = 1) (hb : d184167 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d175218, d184167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44698 q ha hb
    | true =>
      simp only [d175218, d184167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44703 q ha hb
  have h9 (q : Pattern) (ha : d175219 q = 1) (hb : d184168 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d175219, d184168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175219, d184168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d175220 q = 1) (hb : d184169 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d175220, d184169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d175220, d184169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d175221 q = 1) (hb : d184170 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d175221, d184170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d175221, d184170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d175231 q = 1) (hb : d184396 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d175231, d184396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d175231, d184396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d191693 q = 1) (hb : d192211 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191693, d192211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191693, d192211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d191694 q = 1) (hb : d192212 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191694, d192212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191694, d192212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d191695 q = 1) (hb : d192213 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191695, d192213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191695, d192213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d191696 q = 1) (hb : d192214 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191696, d192214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191696, d192214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d191697 q = 1) (hb : d192215 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191697, d192215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d191697, d192215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d191711 q = 1) (hb : d192229 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d191711, d192229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d191711, d192229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d191712 q = 1) (hb : d192230 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d191712, d192230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191712, d192230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d191713 q = 1) (hb : d192231 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d191713, d192231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d191713, d192231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d191723 q = 1) (hb : d192455 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d191723, d192455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d191723, d192455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d191724 q = 1) (hb : d192456 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d191724, d192456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d191724, d192456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro44777 (p : Pattern) (ha : d191730 p = 1) (hb : d192462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191725 q = 1) (hb : d192457 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191725, d192457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44776 q ha hb
    | true =>
      simp only [d191725, d192457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d191726 q = 1) (hb : d192458 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191726, d192458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191726, d192458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d191716 q = 1) (hb : d192234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d191716, d192234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44704 q ha hb
    | true =>
      simp only [d191716, d192234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191717 q = 1) (hb : d192235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d191717, d192235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191717, d192235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d191727 q = 1) (hb : d192459 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d191727, d192459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191727, d192459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191728 q = 1) (hb : d192460 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d191728, d192460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191728, d192460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d191729 q = 1) (hb : d192461 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d191729, d192461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d191729, d192461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d191730 q = 1) (hb : d192462 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d191730, d192462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d191730, d192462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro44778 (p : Pattern) (ha : d191753 p = 1) (hb : d192468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d191722 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d191735 q = 1) (hb : d192463 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d191735, d192463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44777 q ha hb
    | true =>
      simp only [d191735, d192463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44710 q ha hb
  have h3 (q : Pattern) (ha : d191736 q = 1) (hb : d192464 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191736, d192464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191736, d192464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d191749 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d191750 q = 1) (hb : d192465 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191750, d192465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191750, d192465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d191751 q = 1) (hb : d192466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191751, d192466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191751, d192466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d191752 q = 1) (hb : d192467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191752, d192467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191752, d192467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d191753 q = 1) (hb : d192468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191753, d192468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191753, d192468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44779 (p : Pattern) (ha : d191766 p = 1) (hb : d192474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191754 q = 1) (hb : d192469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191754, d192469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191754, d192469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44778 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191761 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d191762 q = 1) (hb : d192470 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d191762, d192470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191762, d192470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d191763 q = 1) (hb : d192471 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d191763, d192471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191763, d192471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191764 q = 1) (hb : d192472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d191764, d192472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191764, d192472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191765 q = 1) (hb : d192473 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d191765, d192473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191765, d192473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d191766 q = 1) (hb : d192474 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d191766, d192474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191766, d192474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44780 (p : Pattern) (ha : d191772 p = 1) (hb : d192480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191767 q = 1) (hb : d192475 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d191767, d192475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191767, d192475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44779 q ha hb
  have h2 (q : Pattern) (ha : d191768 q = 1) (hb : d192476 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d191768, d192476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191768, d192476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d191769 q = 1) (hb : d192477 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d191769, d192477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191769, d192477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d191770 q = 1) (hb : d192478 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d191770, d192478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191770, d192478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d191771 q = 1) (hb : d192479 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d191771, d192479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191771, d192479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191772 q = 1) (hb : d192480 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d191772, d192480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d191772, d192480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44781 (p : Pattern) (ha : d191778 p = 1) (hb : d192486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d191441 q = 1) (hb : d192375 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d191441, d192375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44759 q ha hb
    | true =>
      simp only [d191441, d192375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44762 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d191509 q = 1) (hb : d192394 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d191509, d192394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191509, d192394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44765 q ha hb
  have h3 (q : Pattern) (ha : d191510 q = 1) (hb : d192395 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d191510, d192395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d191510, d192395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d191596 q = 1) (hb : d192422 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d191596, d192422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191596, d192422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44770 q ha hb
  have h5 (q : Pattern) (ha : d191597 q = 1) (hb : d192423 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d191597, d192423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191597, d192423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191598 q = 1) (hb : d192424 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d191598, d192424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191598, d192424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d191684 q = 1) (hb : d192451 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d191684, d192451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191684, d192451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44775 q ha hb
  have h8 (q : Pattern) (ha : d191685 q = 1) (hb : d192452 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d191685, d192452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191685, d192452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d191686 q = 1) (hb : d192453 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d191686, d192453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191686, d192453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d191687 q = 1) (hb : d192454 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d191687, d192454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d191687, d192454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d191773 q = 1) (hb : d192481 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d191773, d192481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191773, d192481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44780 q ha hb
  have h12 (q : Pattern) (ha : d191774 q = 1) (hb : d192482 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d191774, d192482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191774, d192482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d191775 q = 1) (hb : d192483 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d191775, d192483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191775, d192483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d191776 q = 1) (hb : d192484 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d191776, d192484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d191776, d192484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d191777 q = 1) (hb : d192485 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d191777, d192485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d191777, d192485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d191778 q = 1) (hb : d192486 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d191778, d192486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d191778, d192486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro44782 (p : Pattern) (ha : d191784 p = 1) (hb : d192492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191779 q = 1) (hb : d192487 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d191779, d192487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44781 q ha hb
    | true =>
      simp only [d191779, d192487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d191780 q = 1) (hb : d192488 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d191780, d192488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191780, d192488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d191781 q = 1) (hb : d192489 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d191781, d192489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191781, d192489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191782 q = 1) (hb : d192490 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d191782, d192490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191782, d192490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191783 q = 1) (hb : d192491 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d191783, d192491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191783, d192491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191784 q = 1) (hb : d192492 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d191784, d192492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191784, d192492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44783 (p : Pattern) (ha : d191790 p = 1) (hb : d192498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191785 q = 1) (hb : d192493 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d191785, d192493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44782 q ha hb
    | true =>
      simp only [d191785, d192493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d191786 q = 1) (hb : d192494 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d191786, d192494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191786, d192494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d191787 q = 1) (hb : d192495 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d191787, d192495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191787, d192495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191788 q = 1) (hb : d192496 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d191788, d192496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191788, d192496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191789 q = 1) (hb : d192497 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d191789, d192497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191789, d192497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191790 q = 1) (hb : d192498 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d191790, d192498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191790, d192498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44784 (p : Pattern) (ha : d191796 p = 1) (hb : d192504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191791 q = 1) (hb : d192499 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d191791, d192499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44783 q ha hb
    | true =>
      simp only [d191791, d192499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d191792 q = 1) (hb : d192500 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d191792, d192500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191792, d192500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d191793 q = 1) (hb : d192501 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d191793, d192501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191793, d192501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191794 q = 1) (hb : d192502 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d191794, d192502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191794, d192502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191795 q = 1) (hb : d192503 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d191795, d192503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191795, d192503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191796 q = 1) (hb : d192504 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d191796, d192504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191796, d192504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44785 (p : Pattern) (ha : d191802 p = 1) (hb : d192510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191797 q = 1) (hb : d192505 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d191797, d192505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44784 q ha hb
    | true =>
      simp only [d191797, d192505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d191798 q = 1) (hb : d192506 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d191798, d192506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191798, d192506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d191799 q = 1) (hb : d192507 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d191799, d192507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191799, d192507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191800 q = 1) (hb : d192508 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d191800, d192508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191800, d192508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191801 q = 1) (hb : d192509 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d191801, d192509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191801, d192509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191802 q = 1) (hb : d192510 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d191802, d192510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191802, d192510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44786 (p : Pattern) (ha : d191808 p = 1) (hb : d192516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191803 q = 1) (hb : d192511 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d191803, d192511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44785 q ha hb
    | true =>
      simp only [d191803, d192511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d191804 q = 1) (hb : d192512 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d191804, d192512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191804, d192512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d191805 q = 1) (hb : d192513 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d191805, d192513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191805, d192513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191806 q = 1) (hb : d192514 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d191806, d192514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191806, d192514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191807 q = 1) (hb : d192515 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d191807, d192515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191807, d192515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191808 q = 1) (hb : d192516 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d191808, d192516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191808, d192516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44787 (p : Pattern) (ha : d191814 p = 1) (hb : d192522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191809 q = 1) (hb : d192517 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d191809, d192517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44786 q ha hb
    | true =>
      simp only [d191809, d192517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d191810 q = 1) (hb : d192518 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d191810, d192518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191810, d192518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d191811 q = 1) (hb : d192519 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d191811, d192519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191811, d192519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191812 q = 1) (hb : d192520 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d191812, d192520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191812, d192520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191813 q = 1) (hb : d192521 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d191813, d192521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191813, d192521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191814 q = 1) (hb : d192522 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d191814, d192522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191814, d192522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44788 (p : Pattern) (ha : d191820 p = 1) (hb : d192528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191815 q = 1) (hb : d192523 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d191815, d192523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44787 q ha hb
    | true =>
      simp only [d191815, d192523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d191816 q = 1) (hb : d192524 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d191816, d192524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191816, d192524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d191817 q = 1) (hb : d192525 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d191817, d192525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d191817, d192525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d191818 q = 1) (hb : d192526 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d191818, d192526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191818, d192526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d191819 q = 1) (hb : d192527 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d191819, d192527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d191819, d192527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d191820 q = 1) (hb : d192528 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d191820, d192528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d191820, d192528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44789 (p : Pattern) (ha : d191904 p = 1) (hb : d192533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d190669 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191832 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d191900 q = 1) (hb : d192529 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d191900, d192529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d191900, d192529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d190643 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d191901 q = 1) (hb : d192530 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d191901, d192530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d191901, d192530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d191902 q = 1) (hb : d192531 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191902, d192531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d191902, d192531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d191903 q = 1) (hb : d192532 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d191903, d192532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d191903, d192532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d191904 q = 1) (hb : d192533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d191904, d192533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d191904, d192533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44790 (p : Pattern) (ha : d192334 p = 1) (hb : d192539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d191905 q = 1) (hb : d192534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d191905, d192534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d191905, d192534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44789 q ha hb
  have h2 (q : Pattern) (ha : d192330 q = 1) (hb : d192535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192330, d192535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192330, d192535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d192331 q = 1) (hb : d192536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192331, d192536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192331, d192536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d192332 q = 1) (hb : d192537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192332, d192537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192332, d192537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192333 q = 1) (hb : d192538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192333, d192538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192333, d192538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192334 q = 1) (hb : d192539 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192334, d192539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192334, d192539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44791 (p : Pattern) (ha : d192344 p = 1) (hb : d192549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d190709 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191859 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192340 q = 1) (hb : d192545 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192340, d192545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192340, d192545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d190728 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d192341 q = 1) (hb : d192546 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192341, d192546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192341, d192546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192342 q = 1) (hb : d192547 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192342, d192547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192342, d192547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d192343 q = 1) (hb : d192548 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192343, d192548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192343, d192548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d192344 q = 1) (hb : d192549 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192344, d192549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192344, d192549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44792 (p : Pattern) (ha : d192350 p = 1) (hb : d192555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192345 q = 1) (hb : d192550 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192345, d192550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192345, d192550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44791 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d190739 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192346 q = 1) (hb : d192551 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192346, d192551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192346, d192551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192347 q = 1) (hb : d192552 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192347, d192552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192347, d192552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192348 q = 1) (hb : d192553 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192348, d192553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192348, d192553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192349 q = 1) (hb : d192554 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192349, d192554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192349, d192554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d192350 q = 1) (hb : d192555 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192350, d192555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192350, d192555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44793 (p : Pattern) (ha : d192356 p = 1) (hb : d192561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190657 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d192335 q = 1) (hb : d192540 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192335, d192540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192335, d192540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44790 q ha hb
  have h3 (q : Pattern) (ha : d192336 q = 1) (hb : d192541 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192336, d192541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192336, d192541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192337 q = 1) (hb : d192542 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192337, d192542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192337, d192542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d192338 q = 1) (hb : d192543 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192338, d192543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192338, d192543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192339 q = 1) (hb : d192544 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192339, d192544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192339, d192544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d192351 q = 1) (hb : d192556 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192351, d192556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192351, d192556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44792 q ha hb
  have h8 (q : Pattern) (ha : d192352 q = 1) (hb : d192557 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192352, d192557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192352, d192557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d192353 q = 1) (hb : d192558 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192353, d192558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192353, d192558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d192354 q = 1) (hb : d192559 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192354, d192559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192354, d192559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d192355 q = 1) (hb : d192560 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192355, d192560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192355, d192560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d192356 q = 1) (hb : d192561 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192356, d192561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192356, d192561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro44794 (p : Pattern) (ha : d192362 p = 1) (hb : d192566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d190777 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192357 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192358 q = 1) (hb : d192562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192358, d192562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192358, d192562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d190805 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d192359 q = 1) (hb : d192563 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192359, d192563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192359, d192563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192360 q = 1) (hb : d192564 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192360, d192564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192360, d192564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d192361 q = 1) (hb : d192565 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192361, d192565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192361, d192565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d192362 q = 1) (hb : d192566 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192362, d192566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192362, d192566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44795 (p : Pattern) (ha : d192368 p = 1) (hb : d192572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192363 q = 1) (hb : d192567 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192363, d192567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192363, d192567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44794 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d190821 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192364 q = 1) (hb : d192568 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192364, d192568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192364, d192568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192365 q = 1) (hb : d192569 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192365, d192569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192365, d192569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192366 q = 1) (hb : d192570 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192366, d192570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192366, d192570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192367 q = 1) (hb : d192571 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192367, d192571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192367, d192571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d192368 q = 1) (hb : d192572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192368, d192572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192368, d192572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44796 (p : Pattern) (ha : d192374 p = 1) (hb : d192578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192369 q = 1) (hb : d192573 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192369, d192573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192369, d192573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44795 q ha hb
  have h2 (q : Pattern) (ha : d192370 q = 1) (hb : d192574 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192370, d192574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192370, d192574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d192371 q = 1) (hb : d192575 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192371, d192575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192371, d192575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192372 q = 1) (hb : d192576 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192372, d192576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192372, d192576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d192373 q = 1) (hb : d192577 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192373, d192577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192373, d192577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192374 q = 1) (hb : d192578 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192374, d192578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192374, d192578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44797 (p : Pattern) (ha : d192381 p = 1) (hb : d192584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d190865 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192377 q = 1) (hb : d192580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192377, d192580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192377, d192580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d190895 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d192378 q = 1) (hb : d192581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192378, d192581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192378, d192581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192379 q = 1) (hb : d192582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192379, d192582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192379, d192582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d192380 q = 1) (hb : d192583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192380, d192583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192380, d192583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d192381 q = 1) (hb : d192584 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192381, d192584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192381, d192584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44798 (p : Pattern) (ha : d192387 p = 1) (hb : d192590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192382 q = 1) (hb : d192585 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192382, d192585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192382, d192585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44797 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d190911 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192383 q = 1) (hb : d192586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192383, d192586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192383, d192586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192384 q = 1) (hb : d192587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192384, d192587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192384, d192587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192385 q = 1) (hb : d192588 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192385, d192588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192385, d192588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192386 q = 1) (hb : d192589 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192386, d192589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192386, d192589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d192387 q = 1) (hb : d192590 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192387, d192590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192387, d192590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44799 (p : Pattern) (ha : d192393 p = 1) (hb : d192596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192388 q = 1) (hb : d192591 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192388, d192591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192388, d192591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44798 q ha hb
  have h2 (q : Pattern) (ha : d192389 q = 1) (hb : d192592 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192389, d192592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192389, d192592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d192390 q = 1) (hb : d192593 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192390, d192593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192390, d192593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192391 q = 1) (hb : d192594 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192391, d192594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192391, d192594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d192392 q = 1) (hb : d192595 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192392, d192595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192392, d192595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192393 q = 1) (hb : d192596 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192393, d192596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192393, d192596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44800 (p : Pattern) (ha : d192409 p = 1) (hb : d192603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d190959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192405 q = 1) (hb : d192599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192405, d192599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192405, d192599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d190998 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d192406 q = 1) (hb : d192600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192406, d192600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192406, d192600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192407 q = 1) (hb : d192601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192407, d192601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192407, d192601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d192408 q = 1) (hb : d192602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192408, d192602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192408, d192602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d192409 q = 1) (hb : d192603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192409, d192603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192409, d192603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44801 (p : Pattern) (ha : d192415 p = 1) (hb : d192609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192410 q = 1) (hb : d192604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192410, d192604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192410, d192604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44800 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191014 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192411 q = 1) (hb : d192605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192411, d192605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192411, d192605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192412 q = 1) (hb : d192606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192412, d192606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192412, d192606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192413 q = 1) (hb : d192607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192413, d192607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192413, d192607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192414 q = 1) (hb : d192608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192414, d192608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192414, d192608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d192415 q = 1) (hb : d192609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192415, d192609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192415, d192609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44802 (p : Pattern) (ha : d192421 p = 1) (hb : d192615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192416 q = 1) (hb : d192610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192416, d192610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192416, d192610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44801 q ha hb
  have h2 (q : Pattern) (ha : d192417 q = 1) (hb : d192611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192417, d192611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192417, d192611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d192418 q = 1) (hb : d192612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192418, d192612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192418, d192612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192419 q = 1) (hb : d192613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192419, d192613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192419, d192613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d192420 q = 1) (hb : d192614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192420, d192614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192420, d192614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192421 q = 1) (hb : d192615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192421, d192615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192421, d192615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44803 (p : Pattern) (ha : d192438 p = 1) (hb : d192623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d191063 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192433 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192434 q = 1) (hb : d192619 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192434, d192619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192434, d192619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d191102 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d192435 q = 1) (hb : d192620 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192435, d192620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192435, d192620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192436 q = 1) (hb : d192621 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192436, d192621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192436, d192621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d192437 q = 1) (hb : d192622 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192437, d192622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192437, d192622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d192438 q = 1) (hb : d192623 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192438, d192623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192438, d192623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44804 (p : Pattern) (ha : d192444 p = 1) (hb : d192629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192439 q = 1) (hb : d192624 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192439, d192624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192439, d192624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44803 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192440 q = 1) (hb : d192625 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192440, d192625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192440, d192625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192441 q = 1) (hb : d192626 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192441, d192626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192441, d192626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192442 q = 1) (hb : d192627 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192442, d192627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192442, d192627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192443 q = 1) (hb : d192628 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192443, d192628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192443, d192628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d192444 q = 1) (hb : d192629 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192444, d192629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192444, d192629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44805 (p : Pattern) (ha : d192450 p = 1) (hb : d192635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192445 q = 1) (hb : d192630 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192445, d192630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192445, d192630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44804 q ha hb
  have h2 (q : Pattern) (ha : d192446 q = 1) (hb : d192631 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192446, d192631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192446, d192631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d192447 q = 1) (hb : d192632 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192447, d192632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192447, d192632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192448 q = 1) (hb : d192633 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192448, d192633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192448, d192633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d192449 q = 1) (hb : d192634 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192449, d192634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192449, d192634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192450 q = 1) (hb : d192635 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192450, d192635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192450, d192635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44806 (p : Pattern) (ha : d192468 p = 1) (hb : d192644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d191168 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192463 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192464 q = 1) (hb : d192640 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192464, d192640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192464, d192640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d191207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d192465 q = 1) (hb : d192641 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192465, d192641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192465, d192641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192466 q = 1) (hb : d192642 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192466, d192642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192466, d192642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d192467 q = 1) (hb : d192643 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192467, d192643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192467, d192643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d192468 q = 1) (hb : d192644 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192468, d192644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192468, d192644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44807 (p : Pattern) (ha : d192474 p = 1) (hb : d192650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192469 q = 1) (hb : d192645 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192469, d192645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192469, d192645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44806 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d191223 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d192470 q = 1) (hb : d192646 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192470, d192646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192470, d192646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192471 q = 1) (hb : d192647 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192471, d192647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192471, d192647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192472 q = 1) (hb : d192648 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192472, d192648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192472, d192648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192473 q = 1) (hb : d192649 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192473, d192649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192473, d192649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d192474 q = 1) (hb : d192650 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192474, d192650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192474, d192650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44808 (p : Pattern) (ha : d192480 p = 1) (hb : d192656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192475 q = 1) (hb : d192651 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192475, d192651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192475, d192651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44807 q ha hb
  have h2 (q : Pattern) (ha : d192476 q = 1) (hb : d192652 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192476, d192652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192476, d192652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d192477 q = 1) (hb : d192653 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192477, d192653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192477, d192653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192478 q = 1) (hb : d192654 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192478, d192654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192478, d192654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d192479 q = 1) (hb : d192655 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192479, d192655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192479, d192655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192480 q = 1) (hb : d192656 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192480, d192656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192480, d192656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44809 (p : Pattern) (ha : d192486 p = 1) (hb : d192662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d192375 q = 1) (hb : d192579 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192375, d192579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44793 q ha hb
    | true =>
      simp only [d192375, d192579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44796 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d192394 q = 1) (hb : d192597 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192394, d192597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192394, d192597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44799 q ha hb
  have h3 (q : Pattern) (ha : d192395 q = 1) (hb : d192598 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192395, d192598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192395, d192598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d192422 q = 1) (hb : d192616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192422, d192616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192422, d192616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44802 q ha hb
  have h5 (q : Pattern) (ha : d192423 q = 1) (hb : d192617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192423, d192617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192423, d192617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d192424 q = 1) (hb : d192618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192424, d192618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192424, d192618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d192451 q = 1) (hb : d192636 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192451, d192636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192451, d192636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44805 q ha hb
  have h8 (q : Pattern) (ha : d192452 q = 1) (hb : d192637 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192452, d192637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192452, d192637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d192453 q = 1) (hb : d192638 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192453, d192638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192453, d192638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d192454 q = 1) (hb : d192639 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192454, d192639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192454, d192639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d192481 q = 1) (hb : d192657 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192481, d192657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192481, d192657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44808 q ha hb
  have h12 (q : Pattern) (ha : d192482 q = 1) (hb : d192658 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192482, d192658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192482, d192658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d192483 q = 1) (hb : d192659 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192483, d192659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192483, d192659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d192484 q = 1) (hb : d192660 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192484, d192660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192484, d192660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d192485 q = 1) (hb : d192661 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d192485, d192661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d192485, d192661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d192486 q = 1) (hb : d192662 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d192486, d192662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d192486, d192662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro44810 (p : Pattern) (ha : d192492 p = 1) (hb : d192668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192487 q = 1) (hb : d192663 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d192487, d192663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44809 q ha hb
    | true =>
      simp only [d192487, d192663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d192488 q = 1) (hb : d192664 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d192488, d192664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192488, d192664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d192489 q = 1) (hb : d192665 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d192489, d192665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192489, d192665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d192490 q = 1) (hb : d192666 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d192490, d192666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192490, d192666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192491 q = 1) (hb : d192667 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d192491, d192667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192491, d192667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192492 q = 1) (hb : d192668 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d192492, d192668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192492, d192668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44811 (p : Pattern) (ha : d192498 p = 1) (hb : d192674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192493 q = 1) (hb : d192669 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d192493, d192669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44810 q ha hb
    | true =>
      simp only [d192493, d192669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d192494 q = 1) (hb : d192670 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d192494, d192670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192494, d192670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d192495 q = 1) (hb : d192671 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d192495, d192671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192495, d192671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d192496 q = 1) (hb : d192672 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d192496, d192672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192496, d192672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192497 q = 1) (hb : d192673 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d192497, d192673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192497, d192673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192498 q = 1) (hb : d192674 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d192498, d192674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192498, d192674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44812 (p : Pattern) (ha : d192504 p = 1) (hb : d192680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192499 q = 1) (hb : d192675 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d192499, d192675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44811 q ha hb
    | true =>
      simp only [d192499, d192675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d192500 q = 1) (hb : d192676 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d192500, d192676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192500, d192676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d192501 q = 1) (hb : d192677 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d192501, d192677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192501, d192677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d192502 q = 1) (hb : d192678 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d192502, d192678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192502, d192678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192503 q = 1) (hb : d192679 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d192503, d192679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192503, d192679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192504 q = 1) (hb : d192680 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d192504, d192680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192504, d192680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44813 (p : Pattern) (ha : d192510 p = 1) (hb : d192686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192505 q = 1) (hb : d192681 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d192505, d192681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44812 q ha hb
    | true =>
      simp only [d192505, d192681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d192506 q = 1) (hb : d192682 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d192506, d192682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192506, d192682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d192507 q = 1) (hb : d192683 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d192507, d192683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192507, d192683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d192508 q = 1) (hb : d192684 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d192508, d192684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192508, d192684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192509 q = 1) (hb : d192685 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d192509, d192685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192509, d192685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192510 q = 1) (hb : d192686 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d192510, d192686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192510, d192686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44814 (p : Pattern) (ha : d192516 p = 1) (hb : d192692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192511 q = 1) (hb : d192687 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d192511, d192687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44813 q ha hb
    | true =>
      simp only [d192511, d192687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d192512 q = 1) (hb : d192688 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d192512, d192688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192512, d192688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d192513 q = 1) (hb : d192689 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d192513, d192689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192513, d192689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d192514 q = 1) (hb : d192690 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d192514, d192690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192514, d192690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192515 q = 1) (hb : d192691 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d192515, d192691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192515, d192691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192516 q = 1) (hb : d192692 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d192516, d192692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192516, d192692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44815 (p : Pattern) (ha : d192522 p = 1) (hb : d192698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192517 q = 1) (hb : d192693 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d192517, d192693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44814 q ha hb
    | true =>
      simp only [d192517, d192693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d192518 q = 1) (hb : d192694 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d192518, d192694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192518, d192694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d192519 q = 1) (hb : d192695 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d192519, d192695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192519, d192695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d192520 q = 1) (hb : d192696 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d192520, d192696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192520, d192696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192521 q = 1) (hb : d192697 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d192521, d192697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192521, d192697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192522 q = 1) (hb : d192698 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d192522, d192698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192522, d192698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44816 (p : Pattern) (ha : d192528 p = 1) (hb : d192704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d192523 q = 1) (hb : d192699 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d192523, d192699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44815 q ha hb
    | true =>
      simp only [d192523, d192699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d192524 q = 1) (hb : d192700 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d192524, d192700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192524, d192700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d192525 q = 1) (hb : d192701 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d192525, d192701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192525, d192701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d192526 q = 1) (hb : d192702 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d192526, d192702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192526, d192702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d192527 q = 1) (hb : d192703 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d192527, d192703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192527, d192703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d192528 q = 1) (hb : d192704 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d192528, d192704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192528, d192704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44817 (p : Pattern) (ha : d130386 p = 1) (hb : d192712 p = 1) : d130386 p = 1 := by
  have h0 (q : Pattern) (ha : d130386 q = 1) (hb : d192712 q = 1) : d130386 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro44818 (p : Pattern) (ha : d188723 p = 1) (hb : d192712 p = 1) : d188723 p = 1 := by
  have h0 (q : Pattern) (ha : d188723 q = 1) (hb : d192712 q = 1) : d188723 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro44819 (p : Pattern) (ha : d130386 p = 1) (hb : d192716 p = 1) : d130386 p = 1 := by
  have h0 (q : Pattern) (ha : d130386 q = 1) (hb : d192716 q = 1) : d130386 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro44820 (p : Pattern) (ha : d188723 p = 1) (hb : d192716 p = 1) : d188723 p = 1 := by
  have h0 (q : Pattern) (ha : d188723 q = 1) (hb : d192716 q = 1) : d188723 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro44821 (p : Pattern) (ha : d131095 p = 1) (hb : d192717 p = 1) : d131095 p = 1 := by
  have h0 (q : Pattern) (ha : d131095 q = 1) (hb : d192717 q = 1) : d131095 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro44822 (p : Pattern) (ha : d20390 p = 1) (hb : d130483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d51928 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, d51928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, d51928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9300 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9301 q = 1) (hb : d100952 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20390 q = 1) (hb : d130483 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20390, d130483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20390, d130483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44823 (p : Pattern) (ha : d20396 p = 1) (hb : d130489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20391 q = 1) (hb : d130484 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20391, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44822 q ha hb
    | true =>
      simp only [d20391, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20392 q = 1) (hb : d130485 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20392, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20392, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20393 q = 1) (hb : d130486 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20393, d130486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20393, d130486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20394 q = 1) (hb : d130487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20394, d130487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20394, d130487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20395 q = 1) (hb : d130488 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20395, d130488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20395, d130488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20396 q = 1) (hb : d130489 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20396, d130489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20396, d130489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44824 (p : Pattern) (ha : d20402 p = 1) (hb : d130495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20397 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44823 q ha hb
    | true =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20398 q = 1) (hb : d130491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20398, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20398, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20399 q = 1) (hb : d130492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20399, d130492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20399, d130492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20400 q = 1) (hb : d130493 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20400, d130493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20400, d130493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20401 q = 1) (hb : d130494 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20401, d130494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20401, d130494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20402 q = 1) (hb : d130495 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20402, d130495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20402, d130495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44825 (p : Pattern) (ha : d20408 p = 1) (hb : d130501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20403 q = 1) (hb : d130496 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20403, d130496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20403, d130496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44824 q ha hb
  have h2 (q : Pattern) (ha : d20404 q = 1) (hb : d130497 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20404, d130497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20404, d130497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20405 q = 1) (hb : d130498 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20405, d130498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20405, d130498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20406 q = 1) (hb : d130499 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20406, d130499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20406, d130499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20407 q = 1) (hb : d130500 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20407, d130500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20407, d130500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20408 q = 1) (hb : d130501 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20408, d130501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20408, d130501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44826 (p : Pattern) (ha : d20413 p = 1) (hb : d130506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d236 q = 1) (hb : d52054 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236, d52054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h11 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9333 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9300 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9334 q = 1) (hb : d100985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20413 q = 1) (hb : d130506 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20413, d130506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20413, d130506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44827 (p : Pattern) (ha : d20419 p = 1) (hb : d130512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20414 q = 1) (hb : d130507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44826 q ha hb
    | true =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20415 q = 1) (hb : d130508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20391 q = 1) (hb : d130484 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20391, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44822 q ha hb
    | true =>
      simp only [d20391, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20392 q = 1) (hb : d130485 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20392, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20392, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20416 q = 1) (hb : d130509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20416, d130509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20416, d130509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20417 q = 1) (hb : d130510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20417, d130510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20417, d130510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20418 q = 1) (hb : d130511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20418, d130511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20418, d130511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20419 q = 1) (hb : d130512 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20419, d130512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20419, d130512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44828 (p : Pattern) (ha : d130518 p = 1) (hb : d130924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20420 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20420, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44827 q ha hb
    | true =>
      simp only [d20420, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44823 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130514 q = 1) (hb : d130920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130514, d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130514, d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20397 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44823 q ha hb
    | true =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20398 q = 1) (hb : d130491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20398, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20398, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130515 q = 1) (hb : d130921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130515, d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130515, d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d130516 q = 1) (hb : d130922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130516, d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130516, d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130517 q = 1) (hb : d130923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130517, d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130517, d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130518 q = 1) (hb : d130924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130518, d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130518, d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44829 (p : Pattern) (ha : d130524 p = 1) (hb : d130930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130519 q = 1) (hb : d130925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130519, d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130519, d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44828 q ha hb
  have h2 (q : Pattern) (ha : d130520 q = 1) (hb : d130926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130520, d130926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130520, d130926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130521 q = 1) (hb : d130927 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130521, d130927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130521, d130927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130522 q = 1) (hb : d130928 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130522, d130928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130522, d130928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130523 q = 1) (hb : d130929 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130523, d130929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130523, d130929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130524 q = 1) (hb : d130930 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130524, d130930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130524, d130930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44830 (p : Pattern) (ha : d20477 p = 1) (hb : d130554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20397 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44823 q ha hb
    | true =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20473 q = 1) (hb : d130550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20473, d130550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20473, d130550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20474 q = 1) (hb : d130551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20474, d130551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20474, d130551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20475 q = 1) (hb : d130552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20475, d130552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20475, d130552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20476 q = 1) (hb : d130553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20476, d130553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20476, d130553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20477 q = 1) (hb : d130554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20477, d130554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20477, d130554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44831 (p : Pattern) (ha : d20445 p = 1) (hb : d130530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37866 q ha hb
    | true =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16008 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d235 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16009 q = 1) (hb : d126917 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d126917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16009, d126917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h14 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h17 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9333 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9393 q = 1) (hb : d101026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d20445 q = 1) (hb : d130530 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20445, d130530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20445, d130530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44832 (p : Pattern) (ha : d20451 p = 1) (hb : d130536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20446 q = 1) (hb : d130531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20446, d130531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44831 q ha hb
    | true =>
      simp only [d20446, d130531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20447 q = 1) (hb : d130532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20447, d130532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20447, d130532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20414 q = 1) (hb : d130507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44826 q ha hb
    | true =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20415 q = 1) (hb : d130508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20448 q = 1) (hb : d130533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20448, d130533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20448, d130533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20449 q = 1) (hb : d130534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20449, d130534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20449, d130534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20450 q = 1) (hb : d130535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20450, d130535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20450, d130535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20451 q = 1) (hb : d130536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20451, d130536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20451, d130536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44833 (p : Pattern) (ha : d20465 p = 1) (hb : d130542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20414 q = 1) (hb : d130507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44826 q ha hb
    | true =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20415 q = 1) (hb : d130508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20462 q = 1) (hb : d130539 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20462, d130539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20462, d130539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20463 q = 1) (hb : d130540 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20463, d130540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20463, d130540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20464 q = 1) (hb : d130541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20464, d130541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20464, d130541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20465 q = 1) (hb : d130542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20465, d130542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20465, d130542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44834 (p : Pattern) (ha : d130548 p = 1) (hb : d130940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20452 q = 1) (hb : d130537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20452, d130537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44832 q ha hb
    | true =>
      simp only [d20452, d130537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44827 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130538 q = 1) (hb : d130936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130538, d130936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130538, d130936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20466 q = 1) (hb : d130543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20466, d130543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44833 q ha hb
    | true =>
      simp only [d20466, d130543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20467 q = 1) (hb : d130544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20467, d130544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20467, d130544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130545 q = 1) (hb : d130937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130545, d130937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130545, d130937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d130546 q = 1) (hb : d130938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130546, d130938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130546, d130938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130547 q = 1) (hb : d130939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130547, d130939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130547, d130939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130548 q = 1) (hb : d130940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130548, d130940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130548, d130940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44835 (p : Pattern) (ha : d130560 p = 1) (hb : d130946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130549 q = 1) (hb : d130941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130549, d130941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130549, d130941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44834 q ha hb
  have h2 (q : Pattern) (ha : d20478 q = 1) (hb : d130555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, d130555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, d130555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44830 q ha hb
  have h3 (q : Pattern) (ha : d130556 q = 1) (hb : d130942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130556, d130942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130556, d130942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130557 q = 1) (hb : d130943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130557, d130943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130557, d130943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130558 q = 1) (hb : d130944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130558, d130944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130558, d130944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130559 q = 1) (hb : d130945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130559, d130945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130559, d130945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130560 q = 1) (hb : d130946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130560, d130946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130560, d130946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44836 (p : Pattern) (ha : d130566 p = 1) (hb : d130952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20409 q = 1) (hb : d130502 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20409, d130502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20409, d130502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44825 q ha hb
  have h2 (q : Pattern) (ha : d20410 q = 1) (hb : d130503 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20410, d130503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20410, d130503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20411 q = 1) (hb : d130504 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20411, d130504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20411, d130504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20412 q = 1) (hb : d130505 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20412, d130505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20412, d130505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130525 q = 1) (hb : d130931 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130525, d130931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130525, d130931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44829 q ha hb
  have h6 (q : Pattern) (ha : d130526 q = 1) (hb : d130932 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130526, d130932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130526, d130932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130527 q = 1) (hb : d130933 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130527, d130933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130527, d130933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130528 q = 1) (hb : d130934 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130528, d130934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130528, d130934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130529 q = 1) (hb : d130935 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130529, d130935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d130529, d130935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130561 q = 1) (hb : d130947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130561, d130947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130561, d130947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44835 q ha hb
  have h11 (q : Pattern) (ha : d130562 q = 1) (hb : d130948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130562, d130948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130562, d130948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130563 q = 1) (hb : d130949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130563, d130949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130563, d130949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130564 q = 1) (hb : d130950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130564, d130950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130564, d130950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130565 q = 1) (hb : d130951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130565, d130951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130565, d130951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130566 q = 1) (hb : d130952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130566, d130952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130566, d130952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44837 (p : Pattern) (ha : d20500 p = 1) (hb : d130577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d673 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d682 q = 1) (hb : d52386 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d52386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d682, d52386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h7 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9487 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9496 q = 1) (hb : d101111 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20500 q = 1) (hb : d130577 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20500, d130577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20500, d130577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44838 (p : Pattern) (ha : d20538 p = 1) (hb : d130588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20501 q = 1) (hb : d130578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20501, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44837 q ha hb
    | true =>
      simp only [d20501, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20502 q = 1) (hb : d130579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20502, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20502, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20535 q = 1) (hb : d130585 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20535, d130585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20535, d130585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20536 q = 1) (hb : d130586 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20536, d130586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20536, d130586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20537 q = 1) (hb : d130587 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20537, d130587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20537, d130587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20538 q = 1) (hb : d130588 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20538, d130588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20538, d130588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44839 (p : Pattern) (ha : d20544 p = 1) (hb : d130607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20539 q = 1) (hb : d130602 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20539, d130602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44838 q ha hb
    | true =>
      simp only [d20539, d130602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20540 q = 1) (hb : d130603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20540, d130603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20540, d130603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20541 q = 1) (hb : d130604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20541, d130604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20541, d130604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20542 q = 1) (hb : d130605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20542, d130605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20542, d130605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20543 q = 1) (hb : d130606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20543, d130606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20543, d130606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20544 q = 1) (hb : d130607 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20544, d130607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20544, d130607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44840 (p : Pattern) (ha : d20490 p = 1) (hb : d130567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d127054 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d127054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37890 q ha hb
    | true =>
      simp only [d16163, d127054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37866 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d127055 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d127055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d127055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d127056 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d127056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d127056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d127058 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d127058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37866 q ha hb
    | true =>
      simp only [d16167, d127058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37891 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d127059 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d127059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d127059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d127060 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d127060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d127060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d127061 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d127061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d127061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37866 q ha hb
    | true =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h12 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16008 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16171 q = 1) (hb : d127062 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d127062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d127062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9475 q = 1) (hb : d101090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23274 q ha hb
    | true =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
  have h17 (q : Pattern) (ha : d9476 q = 1) (hb : d101091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9477 q = 1) (hb : d101092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9479 q = 1) (hb : d101094 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23275 q ha hb
  have h20 (q : Pattern) (ha : d9480 q = 1) (hb : d101095 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9481 q = 1) (hb : d101096 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9482 q = 1) (hb : d101097 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h24 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h27 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d9483 q = 1) (hb : d101098 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d20490 q = 1) (hb : d130567 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20490, d130567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20490, d130567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro44841 (p : Pattern) (ha : d20493 p = 1) (hb : d130570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d126913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37866 q ha hb
    | true =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d126914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d126915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16008 q = 1) (hb : d126916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d673 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16175 q = 1) (hb : d127066 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d127066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16175, d127066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h11 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h14 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9487 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9488 q = 1) (hb : d101103 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20493 q = 1) (hb : d130570 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20493, d130570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20493, d130570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44842 (p : Pattern) (ha : d20499 p = 1) (hb : d130576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20491 q = 1) (hb : d130568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20491, d130568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44840 q ha hb
    | true =>
      simp only [d20491, d130568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20492 q = 1) (hb : d130569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20492, d130569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20492, d130569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20494 q = 1) (hb : d130571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44841 q ha hb
    | true =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20495 q = 1) (hb : d130572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20496 q = 1) (hb : d130573 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20496, d130573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20496, d130573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20497 q = 1) (hb : d130574 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20497, d130574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20497, d130574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20498 q = 1) (hb : d130575 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20498, d130575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20498, d130575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20499 q = 1) (hb : d130576 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20499, d130576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20499, d130576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44843 (p : Pattern) (ha : d20506 p = 1) (hb : d130583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20494 q = 1) (hb : d130571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44841 q ha hb
    | true =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20495 q = 1) (hb : d130572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20501 q = 1) (hb : d130578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20501, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44837 q ha hb
    | true =>
      simp only [d20501, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20502 q = 1) (hb : d130579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20502, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20502, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20503 q = 1) (hb : d130580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20503, d130580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20503, d130580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20504 q = 1) (hb : d130581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20504, d130581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20504, d130581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20505 q = 1) (hb : d130582 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20505, d130582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20505, d130582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20506 q = 1) (hb : d130583 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20506, d130583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20506, d130583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44844 (p : Pattern) (ha : d20527 p = 1) (hb : d130594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20494 q = 1) (hb : d130571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44841 q ha hb
    | true =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20495 q = 1) (hb : d130572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20524 q = 1) (hb : d130591 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20524, d130591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20524, d130591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20525 q = 1) (hb : d130592 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20525, d130592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20525, d130592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20526 q = 1) (hb : d130593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20526, d130593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20526, d130593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20527 q = 1) (hb : d130594 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20527, d130594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20527, d130594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44845 (p : Pattern) (ha : d130600 p = 1) (hb : d130957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20507 q = 1) (hb : d130584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20507, d130584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44842 q ha hb
    | true =>
      simp only [d20507, d130584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44843 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130590 q = 1) (hb : d130953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130590, d130953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130590, d130953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20528 q = 1) (hb : d130595 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20528, d130595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44844 q ha hb
    | true =>
      simp only [d20528, d130595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20529 q = 1) (hb : d130596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20529, d130596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20529, d130596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130597 q = 1) (hb : d130954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130597, d130954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130597, d130954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d130598 q = 1) (hb : d130955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130598, d130955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130598, d130955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130599 q = 1) (hb : d130956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130599, d130956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130599, d130956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130600 q = 1) (hb : d130957 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130600, d130957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130600, d130957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44846 (p : Pattern) (ha : d130613 p = 1) (hb : d130963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130601 q = 1) (hb : d130958 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130601, d130958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130601, d130958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44845 q ha hb
  have h2 (q : Pattern) (ha : d20545 q = 1) (hb : d130608 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20545, d130608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20545, d130608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44839 q ha hb
  have h3 (q : Pattern) (ha : d130609 q = 1) (hb : d130959 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130609, d130959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130609, d130959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130610 q = 1) (hb : d130960 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130610, d130960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130610, d130960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130611 q = 1) (hb : d130961 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130611, d130961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130611, d130961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130612 q = 1) (hb : d130962 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130612, d130962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130612, d130962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130613 q = 1) (hb : d130963 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130613, d130963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130613, d130963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44847 (p : Pattern) (ha : d130619 p = 1) (hb : d130969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130614 q = 1) (hb : d130964 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130614, d130964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130614, d130964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44846 q ha hb
  have h2 (q : Pattern) (ha : d130615 q = 1) (hb : d130965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130615, d130965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130615, d130965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130616 q = 1) (hb : d130966 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130616, d130966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130616, d130966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130617 q = 1) (hb : d130967 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130617, d130967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130617, d130967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130618 q = 1) (hb : d130968 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130618, d130968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130618, d130968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130619 q = 1) (hb : d130969 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130619, d130969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130619, d130969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44848 (p : Pattern) (ha : d20568 p = 1) (hb : d130631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d52623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d52623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d52623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h7 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9632 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9641 q = 1) (hb : d101221 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20568 q = 1) (hb : d130631 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20568, d130631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20568, d130631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44849 (p : Pattern) (ha : d20606 p = 1) (hb : d130642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20569 q = 1) (hb : d130632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20569, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44848 q ha hb
    | true =>
      simp only [d20569, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20570 q = 1) (hb : d130633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20570, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20570, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20603 q = 1) (hb : d130639 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20603, d130639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20603, d130639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20604 q = 1) (hb : d130640 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20604, d130640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20604, d130640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20605 q = 1) (hb : d130641 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20605, d130641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20605, d130641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20606 q = 1) (hb : d130642 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20606, d130642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20606, d130642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44850 (p : Pattern) (ha : d20612 p = 1) (hb : d130661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20607 q = 1) (hb : d130656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20607, d130656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44849 q ha hb
    | true =>
      simp only [d20607, d130656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20608 q = 1) (hb : d130657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20608, d130657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20608, d130657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20609 q = 1) (hb : d130658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20609, d130658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20609, d130658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20610 q = 1) (hb : d130659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20610, d130659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20610, d130659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20611 q = 1) (hb : d130660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20611, d130660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20611, d130660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20612 q = 1) (hb : d130661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20612, d130661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20612, d130661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44851 (p : Pattern) (ha : d20558 p = 1) (hb : d130621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16364 q = 1) (hb : d127221 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d127221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37918 q ha hb
    | true =>
      simp only [d16364, d127221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37919 q ha hb
  have h2 (q : Pattern) (ha : d16365 q = 1) (hb : d127222 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d127222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16365, d127222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16366 q = 1) (hb : d127223 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d127223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, d127223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16368 q = 1) (hb : d127225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d127225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37919 q ha hb
    | true =>
      simp only [d16368, d127225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37920 q ha hb
  have h5 (q : Pattern) (ha : d16369 q = 1) (hb : d127226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d127226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16369, d127226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16370 q = 1) (hb : d127227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d127227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, d127227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16371 q = 1) (hb : d127228 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d127228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16371, d127228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16372 q = 1) (hb : d127229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37919 q ha hb
    | true =>
      simp only [d16372, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
  have h9 (q : Pattern) (ha : d16373 q = 1) (hb : d127230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16374 q = 1) (hb : d127231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d987 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h12 (q : Pattern) (ha : d988 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d989 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16375 q = 1) (hb : d127232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16375, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16376 q = 1) (hb : d127233 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d127233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16376, d127233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9609 q = 1) (hb : d101189 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23292 q ha hb
    | true =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
  have h17 (q : Pattern) (ha : d9610 q = 1) (hb : d101190 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9611 q = 1) (hb : d101191 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9614 q = 1) (hb : d101194 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23294 q ha hb
  have h20 (q : Pattern) (ha : d9615 q = 1) (hb : d101195 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9616 q = 1) (hb : d101196 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9617 q = 1) (hb : d101197 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h24 (q : Pattern) (ha : d9621 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9622 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h27 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d9627 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d9628 q = 1) (hb : d101208 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d20558 q = 1) (hb : d130621 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20558, d130621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20558, d130621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro44852 (p : Pattern) (ha : d20561 p = 1) (hb : d130624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16372 q = 1) (hb : d127229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37919 q ha hb
    | true =>
      simp only [d16372, d127229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
  have h2 (q : Pattern) (ha : d16373 q = 1) (hb : d127230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d127230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16374 q = 1) (hb : d127231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d127231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d52606 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d52607 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16375 q = 1) (hb : d127232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16375, d127232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d52614 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16380 q = 1) (hb : d127237 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d127237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16380, d127237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h11 (q : Pattern) (ha : d9621 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9622 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h14 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9627 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9632 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9633 q = 1) (hb : d101213 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20561 q = 1) (hb : d130624 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20561, d130624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20561, d130624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44853 (p : Pattern) (ha : d20567 p = 1) (hb : d130630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20559 q = 1) (hb : d130622 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20559, d130622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44851 q ha hb
    | true =>
      simp only [d20559, d130622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20560 q = 1) (hb : d130623 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20560, d130623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20560, d130623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20562 q = 1) (hb : d130625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44852 q ha hb
    | true =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20563 q = 1) (hb : d130626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20564 q = 1) (hb : d130627 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20564, d130627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20564, d130627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20565 q = 1) (hb : d130628 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20565, d130628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20565, d130628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20566 q = 1) (hb : d130629 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20566, d130629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20566, d130629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20567 q = 1) (hb : d130630 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20567, d130630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20567, d130630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44854 (p : Pattern) (ha : d20574 p = 1) (hb : d130637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20562 q = 1) (hb : d130625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44852 q ha hb
    | true =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20563 q = 1) (hb : d130626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20569 q = 1) (hb : d130632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20569, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44848 q ha hb
    | true =>
      simp only [d20569, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20570 q = 1) (hb : d130633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20570, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20570, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20571 q = 1) (hb : d130634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20571, d130634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20571, d130634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20572 q = 1) (hb : d130635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20572, d130635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20572, d130635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20573 q = 1) (hb : d130636 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20573, d130636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20573, d130636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20574 q = 1) (hb : d130637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20574, d130637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20574, d130637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44855 (p : Pattern) (ha : d20595 p = 1) (hb : d130648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20562 q = 1) (hb : d130625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44852 q ha hb
    | true =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20563 q = 1) (hb : d130626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20592 q = 1) (hb : d130645 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20592, d130645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20592, d130645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20593 q = 1) (hb : d130646 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20593, d130646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20593, d130646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20594 q = 1) (hb : d130647 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20594, d130647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20594, d130647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20595 q = 1) (hb : d130648 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20595, d130648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20595, d130648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44856 (p : Pattern) (ha : d130654 p = 1) (hb : d130975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20575 q = 1) (hb : d130638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20575, d130638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44853 q ha hb
    | true =>
      simp only [d20575, d130638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44854 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130643 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130644 q = 1) (hb : d130971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130644, d130971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130644, d130971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20596 q = 1) (hb : d130649 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20596, d130649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44855 q ha hb
    | true =>
      simp only [d20596, d130649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20597 q = 1) (hb : d130650 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20597, d130650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20597, d130650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130651 q = 1) (hb : d130972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130651, d130972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130651, d130972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d130652 q = 1) (hb : d130973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130652, d130973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130652, d130973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130653 q = 1) (hb : d130974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130653, d130974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130653, d130974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130654 q = 1) (hb : d130975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130654, d130975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130654, d130975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44857 (p : Pattern) (ha : d130667 p = 1) (hb : d130981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130655 q = 1) (hb : d130976 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130655, d130976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130655, d130976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44856 q ha hb
  have h2 (q : Pattern) (ha : d20613 q = 1) (hb : d130662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20613, d130662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20613, d130662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44850 q ha hb
  have h3 (q : Pattern) (ha : d130663 q = 1) (hb : d130977 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130663, d130977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130663, d130977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130664 q = 1) (hb : d130978 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130664, d130978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130664, d130978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130665 q = 1) (hb : d130979 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130665, d130979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130665, d130979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130666 q = 1) (hb : d130980 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130666, d130980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130666, d130980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130667 q = 1) (hb : d130981 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130667, d130981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130667, d130981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44858 (p : Pattern) (ha : d130673 p = 1) (hb : d130987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130668 q = 1) (hb : d130982 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130668, d130982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130668, d130982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44857 q ha hb
  have h2 (q : Pattern) (ha : d130669 q = 1) (hb : d130983 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130669, d130983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130669, d130983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130670 q = 1) (hb : d130984 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130670, d130984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130670, d130984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130671 q = 1) (hb : d130985 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130671, d130985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130671, d130985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130672 q = 1) (hb : d130986 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130672, d130986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130672, d130986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130673 q = 1) (hb : d130987 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130673, d130987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130673, d130987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44859 (p : Pattern) (ha : d20637 p = 1) (hb : d130686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16693 q = 1) (hb : d127494 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
    | true =>
      simp only [d16693, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33858 q ha hb
  have h2 (q : Pattern) (ha : d16694 q = 1) (hb : d127495 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16695 q = 1) (hb : d127496 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16696 q = 1) (hb : d127497 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16696, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16697 q = 1) (hb : d127498 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, d127498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16697, d127498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h7 (q : Pattern) (ha : d9871 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9872 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9873 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9874 q = 1) (hb : d101395 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20637 q = 1) (hb : d130686 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20637, d130686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20637, d130686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44860 (p : Pattern) (ha : d20678 p = 1) (hb : d130704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20638 q = 1) (hb : d130687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44859 q ha hb
    | true =>
      simp only [d20638, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20639 q = 1) (hb : d130688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20675 q = 1) (hb : d130701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20675, d130701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20675, d130701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20676 q = 1) (hb : d130702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20676, d130702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20676, d130702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20677 q = 1) (hb : d130703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20677, d130703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20677, d130703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20678 q = 1) (hb : d130704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20678, d130704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20678, d130704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44861 (p : Pattern) (ha : d20684 p = 1) (hb : d130726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20679 q = 1) (hb : d130721 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20679, d130721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44860 q ha hb
    | true =>
      simp only [d20679, d130721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20680 q = 1) (hb : d130722 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20680, d130722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20680, d130722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20681 q = 1) (hb : d130723 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20681, d130723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20681, d130723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20682 q = 1) (hb : d130724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20682, d130724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20682, d130724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20683 q = 1) (hb : d130725 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20683, d130725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20683, d130725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20684 q = 1) (hb : d130726 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20684, d130726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20684, d130726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44862 (p : Pattern) (ha : d20627 p = 1) (hb : d130676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16663 q = 1) (hb : d127464 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16663, d127464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37964 q ha hb
    | true =>
      simp only [d16663, d127464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37965 q ha hb
  have h2 (q : Pattern) (ha : d16664 q = 1) (hb : d127465 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d127465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16664, d127465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16665 q = 1) (hb : d127466 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, d127466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, d127466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16668 q = 1) (hb : d127469 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16668, d127469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37965 q ha hb
    | true =>
      simp only [d16668, d127469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37966 q ha hb
  have h5 (q : Pattern) (ha : d16669 q = 1) (hb : d127470 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d127470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16669, d127470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16670 q = 1) (hb : d127471 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, d127471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, d127471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16671 q = 1) (hb : d127472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, d127472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16671, d127472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16673 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37965 q ha hb
    | true =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
  have h9 (q : Pattern) (ha : d16674 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16675 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16676 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
    | true =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33885 q ha hb
  have h12 (q : Pattern) (ha : d16677 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16678 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16679 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16680 q = 1) (hb : d127481 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, d127481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16680, d127481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9807 q = 1) (hb : d101328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23314 q ha hb
    | true =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
  have h17 (q : Pattern) (ha : d9808 q = 1) (hb : d101329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9809 q = 1) (hb : d101330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9822 q = 1) (hb : d101343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23318 q ha hb
  have h20 (q : Pattern) (ha : d9823 q = 1) (hb : d101344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9824 q = 1) (hb : d101345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d9825 q = 1) (hb : d101346 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h24 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h27 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d9855 q = 1) (hb : d101376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d20627 q = 1) (hb : d130676 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20627, d130676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20627, d130676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro44863 (p : Pattern) (ha : d20630 p = 1) (hb : d130679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37965 q ha hb
    | true =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
    | true =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33885 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16684 q = 1) (hb : d127485 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, d127485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16684, d127485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16685 q = 1) (hb : d127486 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, d127486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16685, d127486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h11 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h14 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9859 q = 1) (hb : d101380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9860 q = 1) (hb : d101381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20630 q = 1) (hb : d130679 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20630, d130679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20630, d130679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44864 (p : Pattern) (ha : d20636 p = 1) (hb : d130685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20628 q = 1) (hb : d130677 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20628, d130677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44862 q ha hb
    | true =>
      simp only [d20628, d130677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20629 q = 1) (hb : d130678 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20629, d130678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20629, d130678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20631 q = 1) (hb : d130680 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44863 q ha hb
    | true =>
      simp only [d20631, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20632 q = 1) (hb : d130681 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20632, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20633 q = 1) (hb : d130682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20633, d130682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20633, d130682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20634 q = 1) (hb : d130683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20634, d130683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20634, d130683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20635 q = 1) (hb : d130684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20635, d130684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20635, d130684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20636 q = 1) (hb : d130685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20636, d130685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20636, d130685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44865 (p : Pattern) (ha : d20643 p = 1) (hb : d130692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20631 q = 1) (hb : d130680 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44863 q ha hb
    | true =>
      simp only [d20631, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20632 q = 1) (hb : d130681 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20632, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d130687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44859 q ha hb
    | true =>
      simp only [d20638, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d130688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20640 q = 1) (hb : d130689 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20640, d130689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20640, d130689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20641 q = 1) (hb : d130690 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20641, d130690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20641, d130690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20642 q = 1) (hb : d130691 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20642, d130691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20642, d130691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20643 q = 1) (hb : d130692 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20643, d130692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20643, d130692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44866 (p : Pattern) (ha : d20661 p = 1) (hb : d130707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37965 q ha hb
    | true =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
    | true =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33885 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16743 q = 1) (hb : d127521 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d127521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
    | true =>
      simp only [d16743, d127521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18640 q ha hb
  have h9 (q : Pattern) (ha : d16744 q = 1) (hb : d127522 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d127522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16744, d127522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16745 q = 1) (hb : d127523 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d127523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, d127523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16746 q = 1) (hb : d127524 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d127524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16746, d127524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16747 q = 1) (hb : d127525 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d127525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16747, d127525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h14 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h17 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9988 q = 1) (hb : d101419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23324 q ha hb
  have h21 (q : Pattern) (ha : d9989 q = 1) (hb : d101420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9990 q = 1) (hb : d101421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9991 q = 1) (hb : d101422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9992 q = 1) (hb : d101423 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d20661 q = 1) (hb : d130707 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20661, d130707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20661, d130707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44867 (p : Pattern) (ha : d20667 p = 1) (hb : d130713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20662 q = 1) (hb : d130708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20662, d130708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44866 q ha hb
    | true =>
      simp only [d20662, d130708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20663 q = 1) (hb : d130709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20663, d130709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20663, d130709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20664 q = 1) (hb : d130710 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20664, d130710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20664, d130710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20665 q = 1) (hb : d130711 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20665, d130711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20665, d130711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20666 q = 1) (hb : d130712 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20666, d130712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20666, d130712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20667 q = 1) (hb : d130713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20667, d130713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20667, d130713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44868 (p : Pattern) (ha : d130719 p = 1) (hb : d130994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20644 q = 1) (hb : d130693 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20644, d130693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44864 q ha hb
    | true =>
      simp only [d20644, d130693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44865 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130706 q = 1) (hb : d130990 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130706, d130990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130706, d130990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20668 q = 1) (hb : d130714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20668, d130714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44867 q ha hb
    | true =>
      simp only [d20668, d130714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20669 q = 1) (hb : d130715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20669, d130715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20669, d130715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130716 q = 1) (hb : d130991 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130716, d130991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130716, d130991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d130717 q = 1) (hb : d130992 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130717, d130992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130717, d130992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130718 q = 1) (hb : d130993 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130718, d130993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130718, d130993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130719 q = 1) (hb : d130994 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130719, d130994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130719, d130994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44869 (p : Pattern) (ha : d130732 p = 1) (hb : d131000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130720 q = 1) (hb : d130995 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130720, d130995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130720, d130995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44868 q ha hb
  have h2 (q : Pattern) (ha : d20685 q = 1) (hb : d130727 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20685, d130727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20685, d130727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44861 q ha hb
  have h3 (q : Pattern) (ha : d130728 q = 1) (hb : d130996 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130728, d130996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130728, d130996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130729 q = 1) (hb : d130997 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130729, d130997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130729, d130997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130730 q = 1) (hb : d130998 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130730, d130998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130730, d130998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130731 q = 1) (hb : d130999 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130731, d130999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130731, d130999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130732 q = 1) (hb : d131000 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130732, d131000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130732, d131000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44870 (p : Pattern) (ha : d130738 p = 1) (hb : d131006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130733 q = 1) (hb : d131001 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130733, d131001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130733, d131001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44869 q ha hb
  have h2 (q : Pattern) (ha : d130734 q = 1) (hb : d131002 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130734, d131002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130734, d131002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130735 q = 1) (hb : d131003 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130735, d131003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130735, d131003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130736 q = 1) (hb : d131004 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130736, d131004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130736, d131004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130737 q = 1) (hb : d131005 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130737, d131005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130737, d131005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130738 q = 1) (hb : d131006 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130738, d131006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130738, d131006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44871 (p : Pattern) (ha : d20710 p = 1) (hb : d130752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17053 q = 1) (hb : d127787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
    | true =>
      simp only [d17053, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33911 q ha hb
  have h2 (q : Pattern) (ha : d17054 q = 1) (hb : d127788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17055 q = 1) (hb : d127789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17056 q = 1) (hb : d127790 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17056, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17057 q = 1) (hb : d127791 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d127791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17057, d127791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h7 (q : Pattern) (ha : d10165 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10166 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10167 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10168 q = 1) (hb : d101595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20710 q = 1) (hb : d130752 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20710, d130752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20710, d130752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44872 (p : Pattern) (ha : d20751 p = 1) (hb : d130770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20711 q = 1) (hb : d130753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44871 q ha hb
    | true =>
      simp only [d20711, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20712 q = 1) (hb : d130754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20748 q = 1) (hb : d130767 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20748, d130767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20748, d130767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20749 q = 1) (hb : d130768 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20749, d130768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20749, d130768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20750 q = 1) (hb : d130769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20750, d130769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20750, d130769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20751 q = 1) (hb : d130770 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20751, d130770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20751, d130770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44873 (p : Pattern) (ha : d20757 p = 1) (hb : d130792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20752 q = 1) (hb : d130787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20752, d130787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44872 q ha hb
    | true =>
      simp only [d20752, d130787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20753 q = 1) (hb : d130788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20753, d130788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20753, d130788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20754 q = 1) (hb : d130789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20754, d130789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20754, d130789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20755 q = 1) (hb : d130790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20755, d130790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20755, d130790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20756 q = 1) (hb : d130791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20756, d130791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20756, d130791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20757 q = 1) (hb : d130792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20757, d130792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20757, d130792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44874 (p : Pattern) (ha : d20700 p = 1) (hb : d130742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17018 q = 1) (hb : d127752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17018, d127752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38011 q ha hb
    | true =>
      simp only [d17018, d127752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38012 q ha hb
  have h2 (q : Pattern) (ha : d17019 q = 1) (hb : d127753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d127753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17019, d127753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17020 q = 1) (hb : d127754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, d127754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, d127754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17023 q = 1) (hb : d127757 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17023, d127757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38012 q ha hb
    | true =>
      simp only [d17023, d127757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38013 q ha hb
  have h5 (q : Pattern) (ha : d17024 q = 1) (hb : d127758 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d127758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17024, d127758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17025 q = 1) (hb : d127759 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, d127759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, d127759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17026 q = 1) (hb : d127760 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, d127760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17026, d127760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17033 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38012 q ha hb
    | true =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
  have h9 (q : Pattern) (ha : d17034 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17035 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17036 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
    | true =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33938 q ha hb
  have h12 (q : Pattern) (ha : d17037 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17038 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17039 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17040 q = 1) (hb : d127774 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, d127774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17040, d127774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10092 q = 1) (hb : d101519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23342 q ha hb
    | true =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
  have h17 (q : Pattern) (ha : d10093 q = 1) (hb : d101520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10094 q = 1) (hb : d101521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10107 q = 1) (hb : d101534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23346 q ha hb
  have h20 (q : Pattern) (ha : d10108 q = 1) (hb : d101535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10109 q = 1) (hb : d101536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10110 q = 1) (hb : d101537 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h24 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h27 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d10146 q = 1) (hb : d101573 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d20700 q = 1) (hb : d130742 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20700, d130742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20700, d130742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro44875 (p : Pattern) (ha : d20703 p = 1) (hb : d130745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38012 q ha hb
    | true =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
    | true =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33938 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17044 q = 1) (hb : d127778 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, d127778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17044, d127778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17045 q = 1) (hb : d127779 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, d127779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17045, d127779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h11 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h14 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10150 q = 1) (hb : d101577 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10151 q = 1) (hb : d101578 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20703 q = 1) (hb : d130745 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20703, d130745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20703, d130745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44876 (p : Pattern) (ha : d20709 p = 1) (hb : d130751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20701 q = 1) (hb : d130743 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20701, d130743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44874 q ha hb
    | true =>
      simp only [d20701, d130743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20702 q = 1) (hb : d130744 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20702, d130744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20702, d130744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20704 q = 1) (hb : d130746 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44875 q ha hb
    | true =>
      simp only [d20704, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20705 q = 1) (hb : d130747 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20705, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20706 q = 1) (hb : d130748 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20706, d130748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20706, d130748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20707 q = 1) (hb : d130749 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20707, d130749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20707, d130749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20708 q = 1) (hb : d130750 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20708, d130750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20708, d130750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20709 q = 1) (hb : d130751 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20709, d130751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20709, d130751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44877 (p : Pattern) (ha : d20716 p = 1) (hb : d130758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20704 q = 1) (hb : d130746 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44875 q ha hb
    | true =>
      simp only [d20704, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20705 q = 1) (hb : d130747 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20705, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d130753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44871 q ha hb
    | true =>
      simp only [d20711, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d130754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20713 q = 1) (hb : d130755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20713, d130755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20713, d130755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20714 q = 1) (hb : d130756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20714, d130756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20714, d130756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20715 q = 1) (hb : d130757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20715, d130757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20715, d130757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20716 q = 1) (hb : d130758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20716, d130758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20716, d130758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44878 (p : Pattern) (ha : d20734 p = 1) (hb : d130773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38012 q ha hb
    | true =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
    | true =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33938 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17108 q = 1) (hb : d127814 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17108, d127814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
    | true =>
      simp only [d17108, d127814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18688 q ha hb
  have h9 (q : Pattern) (ha : d17109 q = 1) (hb : d127815 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d127815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17109, d127815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17110 q = 1) (hb : d127816 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, d127816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, d127816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17111 q = 1) (hb : d127817 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, d127817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17111, d127817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17112 q = 1) (hb : d127818 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, d127818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17112, d127818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h14 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h17 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10294 q = 1) (hb : d101619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23352 q ha hb
  have h21 (q : Pattern) (ha : d10295 q = 1) (hb : d101620 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10296 q = 1) (hb : d101621 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10297 q = 1) (hb : d101622 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10298 q = 1) (hb : d101623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d20734 q = 1) (hb : d130773 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20734, d130773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20734, d130773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44879 (p : Pattern) (ha : d20740 p = 1) (hb : d130779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20735 q = 1) (hb : d130774 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20735, d130774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44878 q ha hb
    | true =>
      simp only [d20735, d130774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20736 q = 1) (hb : d130775 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20736, d130775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20736, d130775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20737 q = 1) (hb : d130776 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20737, d130776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20737, d130776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20738 q = 1) (hb : d130777 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20738, d130777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20738, d130777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20739 q = 1) (hb : d130778 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20739, d130778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20739, d130778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20740 q = 1) (hb : d130779 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20740, d130779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20740, d130779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44880 (p : Pattern) (ha : d130785 p = 1) (hb : d131014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20717 q = 1) (hb : d130759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20717, d130759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44876 q ha hb
    | true =>
      simp only [d20717, d130759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44877 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130772 q = 1) (hb : d131010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130772, d131010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130772, d131010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20741 q = 1) (hb : d130780 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20741, d130780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44879 q ha hb
    | true =>
      simp only [d20741, d130780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20742 q = 1) (hb : d130781 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20742, d130781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20742, d130781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130782 q = 1) (hb : d131011 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130782, d131011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130782, d131011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d130783 q = 1) (hb : d131012 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130783, d131012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130783, d131012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130784 q = 1) (hb : d131013 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130784, d131013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130784, d131013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130785 q = 1) (hb : d131014 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130785, d131014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130785, d131014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44881 (p : Pattern) (ha : d130798 p = 1) (hb : d131020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130786 q = 1) (hb : d131015 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130786, d131015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130786, d131015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44880 q ha hb
  have h2 (q : Pattern) (ha : d20758 q = 1) (hb : d130793 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20758, d130793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20758, d130793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44873 q ha hb
  have h3 (q : Pattern) (ha : d130794 q = 1) (hb : d131016 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130794, d131016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130794, d131016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130795 q = 1) (hb : d131017 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130795, d131017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130795, d131017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130796 q = 1) (hb : d131018 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130796, d131018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130796, d131018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130797 q = 1) (hb : d131019 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130797, d131019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130797, d131019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130798 q = 1) (hb : d131020 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130798, d131020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130798, d131020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44882 (p : Pattern) (ha : d130804 p = 1) (hb : d131026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130799 q = 1) (hb : d131021 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130799, d131021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130799, d131021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44881 q ha hb
  have h2 (q : Pattern) (ha : d130800 q = 1) (hb : d131022 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130800, d131022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130800, d131022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130801 q = 1) (hb : d131023 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130801, d131023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130801, d131023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130802 q = 1) (hb : d131024 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130802, d131024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130802, d131024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130803 q = 1) (hb : d131025 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130803, d131025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130803, d131025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130804 q = 1) (hb : d131026 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130804, d131026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130804, d131026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44883 (p : Pattern) (ha : d20784 p = 1) (hb : d130819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17417 q = 1) (hb : d128079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
    | true =>
      simp only [d17417, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33964 q ha hb
  have h2 (q : Pattern) (ha : d17418 q = 1) (hb : d128080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17419 q = 1) (hb : d128081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17420 q = 1) (hb : d128082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17420, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17421 q = 1) (hb : d128083 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, d128083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17421, d128083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h7 (q : Pattern) (ha : d10442 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10443 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10444 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10445 q = 1) (hb : d101766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20784 q = 1) (hb : d130819 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20784, d130819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20784, d130819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44884 (p : Pattern) (ha : d20825 p = 1) (hb : d130837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20785 q = 1) (hb : d130820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44883 q ha hb
    | true =>
      simp only [d20785, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20786 q = 1) (hb : d130821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20822 q = 1) (hb : d130834 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20822, d130834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20822, d130834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20823 q = 1) (hb : d130835 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20823, d130835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20823, d130835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20824 q = 1) (hb : d130836 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20824, d130836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20824, d130836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20825 q = 1) (hb : d130837 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20825, d130837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20825, d130837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44885 (p : Pattern) (ha : d20831 p = 1) (hb : d130859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20826 q = 1) (hb : d130854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20826, d130854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44884 q ha hb
    | true =>
      simp only [d20826, d130854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20827 q = 1) (hb : d130855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20827, d130855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20827, d130855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20828 q = 1) (hb : d130856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20828, d130856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20828, d130856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20829 q = 1) (hb : d130857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20829, d130857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20829, d130857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20830 q = 1) (hb : d130858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20830, d130858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20830, d130858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20831 q = 1) (hb : d130859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20831, d130859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20831, d130859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44886 (p : Pattern) (ha : d20774 p = 1) (hb : d130809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17383 q = 1) (hb : d128045 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d128045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38058 q ha hb
    | true =>
      simp only [d17383, d128045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38059 q ha hb
  have h2 (q : Pattern) (ha : d17384 q = 1) (hb : d128046 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d128046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17384, d128046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17385 q = 1) (hb : d128047 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d128047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, d128047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17387 q = 1) (hb : d128049 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d128049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38059 q ha hb
    | true =>
      simp only [d17387, d128049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38060 q ha hb
  have h5 (q : Pattern) (ha : d17388 q = 1) (hb : d128050 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d128050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17388, d128050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17389 q = 1) (hb : d128051 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d128051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, d128051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17390 q = 1) (hb : d128052 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d128052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17390, d128052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17397 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38059 q ha hb
    | true =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
  have h9 (q : Pattern) (ha : d17398 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17399 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17400 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
    | true =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33991 q ha hb
  have h12 (q : Pattern) (ha : d17401 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17402 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17403 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17404 q = 1) (hb : d128066 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d128066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17404, d128066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10378 q = 1) (hb : d101699 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23368 q ha hb
    | true =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
  have h17 (q : Pattern) (ha : d10379 q = 1) (hb : d101700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10380 q = 1) (hb : d101701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10383 q = 1) (hb : d101704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23371 q ha hb
  have h20 (q : Pattern) (ha : d10384 q = 1) (hb : d101705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10385 q = 1) (hb : d101706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10386 q = 1) (hb : d101707 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h24 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h27 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d10423 q = 1) (hb : d101744 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d20774 q = 1) (hb : d130809 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20774, d130809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20774, d130809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro44887 (p : Pattern) (ha : d20777 p = 1) (hb : d130812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38059 q ha hb
    | true =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
    | true =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33991 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17408 q = 1) (hb : d128070 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d128070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17408, d128070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17409 q = 1) (hb : d128071 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d128071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17409, d128071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h11 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h14 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10427 q = 1) (hb : d101748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10428 q = 1) (hb : d101749 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d20777 q = 1) (hb : d130812 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20777, d130812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20777, d130812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro44888 (p : Pattern) (ha : d20783 p = 1) (hb : d130818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20775 q = 1) (hb : d130810 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20775, d130810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44886 q ha hb
    | true =>
      simp only [d20775, d130810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20776 q = 1) (hb : d130811 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20776, d130811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20776, d130811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20778 q = 1) (hb : d130813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44887 q ha hb
    | true =>
      simp only [d20778, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20779 q = 1) (hb : d130814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20779, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20780 q = 1) (hb : d130815 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20780, d130815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20780, d130815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20781 q = 1) (hb : d130816 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20781, d130816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20781, d130816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20782 q = 1) (hb : d130817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20782, d130817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20782, d130817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20783 q = 1) (hb : d130818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20783, d130818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20783, d130818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44889 (p : Pattern) (ha : d20790 p = 1) (hb : d130825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20778 q = 1) (hb : d130813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44887 q ha hb
    | true =>
      simp only [d20778, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20779 q = 1) (hb : d130814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20779, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d130820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44883 q ha hb
    | true =>
      simp only [d20785, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d130821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20787 q = 1) (hb : d130822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20787, d130822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20787, d130822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20788 q = 1) (hb : d130823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20788, d130823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20788, d130823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20789 q = 1) (hb : d130824 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20789, d130824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20789, d130824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20790 q = 1) (hb : d130825 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20790, d130825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20790, d130825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44890 (p : Pattern) (ha : d20808 p = 1) (hb : d130840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38059 q ha hb
    | true =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
    | true =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33991 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17472 q = 1) (hb : d128106 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17472, d128106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
    | true =>
      simp only [d17472, d128106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18736 q ha hb
  have h9 (q : Pattern) (ha : d17473 q = 1) (hb : d128107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d128107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17473, d128107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17474 q = 1) (hb : d128108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, d128108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, d128108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17475 q = 1) (hb : d128109 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, d128109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17475, d128109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17476 q = 1) (hb : d128110 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, d128110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17476, d128110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h14 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h17 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10560 q = 1) (hb : d101790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23377 q ha hb
  have h21 (q : Pattern) (ha : d10561 q = 1) (hb : d101791 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10562 q = 1) (hb : d101792 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10563 q = 1) (hb : d101793 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10564 q = 1) (hb : d101794 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d20808 q = 1) (hb : d130840 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20808, d130840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20808, d130840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44891 (p : Pattern) (ha : d20814 p = 1) (hb : d130846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20809 q = 1) (hb : d130841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20809, d130841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44890 q ha hb
    | true =>
      simp only [d20809, d130841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20810 q = 1) (hb : d130842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20810, d130842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20810, d130842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20811 q = 1) (hb : d130843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20811, d130843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20811, d130843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20812 q = 1) (hb : d130844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20812, d130844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20812, d130844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20813 q = 1) (hb : d130845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20813, d130845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20813, d130845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20814 q = 1) (hb : d130846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20814, d130846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20814, d130846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44892 (p : Pattern) (ha : d130852 p = 1) (hb : d131035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20791 q = 1) (hb : d130826 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20791, d130826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44888 q ha hb
    | true =>
      simp only [d20791, d130826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44889 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130838 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130839 q = 1) (hb : d131031 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130839, d131031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130839, d131031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20815 q = 1) (hb : d130847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20815, d130847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44891 q ha hb
    | true =>
      simp only [d20815, d130847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20816 q = 1) (hb : d130848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20816, d130848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20816, d130848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130849 q = 1) (hb : d131032 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130849, d131032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130849, d131032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d130850 q = 1) (hb : d131033 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130850, d131033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130850, d131033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130851 q = 1) (hb : d131034 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130851, d131034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130851, d131034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130852 q = 1) (hb : d131035 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130852, d131035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130852, d131035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro44893 (p : Pattern) (ha : d130865 p = 1) (hb : d131041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130853 q = 1) (hb : d131036 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130853, d131036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130853, d131036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44892 q ha hb
  have h2 (q : Pattern) (ha : d20832 q = 1) (hb : d130860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20832, d130860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20832, d130860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44885 q ha hb
  have h3 (q : Pattern) (ha : d130861 q = 1) (hb : d131037 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130861, d131037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130861, d131037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130862 q = 1) (hb : d131038 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130862, d131038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130862, d131038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130863 q = 1) (hb : d131039 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130863, d131039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130863, d131039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130864 q = 1) (hb : d131040 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130864, d131040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130864, d131040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130865 q = 1) (hb : d131041 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130865, d131041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130865, d131041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44894 (p : Pattern) (ha : d130871 p = 1) (hb : d131047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130866 q = 1) (hb : d131042 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130866, d131042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130866, d131042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44893 q ha hb
  have h2 (q : Pattern) (ha : d130867 q = 1) (hb : d131043 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130867, d131043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130867, d131043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130868 q = 1) (hb : d131044 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130868, d131044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130868, d131044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130869 q = 1) (hb : d131045 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130869, d131045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130869, d131045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130870 q = 1) (hb : d131046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130870, d131046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130870, d131046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130871 q = 1) (hb : d131047 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130871, d131047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130871, d131047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44895 (p : Pattern) (ha : d130877 p = 1) (hb : d131053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130620 q = 1) (hb : d130970 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130620, d130970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44836 q ha hb
    | true =>
      simp only [d130620, d130970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44847 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130674 q = 1) (hb : d130988 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130674, d130988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130674, d130988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44858 q ha hb
  have h3 (q : Pattern) (ha : d130675 q = 1) (hb : d130989 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130675, d130989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130675, d130989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130739 q = 1) (hb : d131007 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130739, d131007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130739, d131007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44870 q ha hb
  have h5 (q : Pattern) (ha : d130740 q = 1) (hb : d131008 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130740, d131008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130740, d131008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130741 q = 1) (hb : d131009 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130741, d131009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130741, d131009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130805 q = 1) (hb : d131027 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130805, d131027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130805, d131027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44882 q ha hb
  have h8 (q : Pattern) (ha : d130806 q = 1) (hb : d131028 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130806, d131028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130806, d131028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130807 q = 1) (hb : d131029 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130807, d131029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130807, d131029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130808 q = 1) (hb : d131030 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130808, d131030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130808, d131030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130872 q = 1) (hb : d131048 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130872, d131048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130872, d131048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44894 q ha hb
  have h12 (q : Pattern) (ha : d130873 q = 1) (hb : d131049 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130873, d131049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130873, d131049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130874 q = 1) (hb : d131050 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130874, d131050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130874, d131050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130875 q = 1) (hb : d131051 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130875, d131051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130875, d131051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130876 q = 1) (hb : d131052 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130876, d131052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130876, d131052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130877 q = 1) (hb : d131053 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130877, d131053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130877, d131053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro44896 (p : Pattern) (ha : d130883 p = 1) (hb : d131059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130878 q = 1) (hb : d131054 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130878, d131054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44895 q ha hb
    | true =>
      simp only [d130878, d131054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130879 q = 1) (hb : d131055 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130879, d131055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130879, d131055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130880 q = 1) (hb : d131056 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130880, d131056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130880, d131056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130881 q = 1) (hb : d131057 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130881, d131057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130881, d131057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130882 q = 1) (hb : d131058 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130882, d131058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130882, d131058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130883 q = 1) (hb : d131059 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130883, d131059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130883, d131059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44897 (p : Pattern) (ha : d130889 p = 1) (hb : d131065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130884 q = 1) (hb : d131060 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130884, d131060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44896 q ha hb
    | true =>
      simp only [d130884, d131060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130885 q = 1) (hb : d131061 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130885, d131061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130885, d131061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130886 q = 1) (hb : d131062 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130886, d131062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130886, d131062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130887 q = 1) (hb : d131063 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130887, d131063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130887, d131063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130888 q = 1) (hb : d131064 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130888, d131064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130888, d131064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130889 q = 1) (hb : d131065 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130889, d131065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130889, d131065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44898 (p : Pattern) (ha : d130895 p = 1) (hb : d131071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130890 q = 1) (hb : d131066 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130890, d131066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44897 q ha hb
    | true =>
      simp only [d130890, d131066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130891 q = 1) (hb : d131067 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130891, d131067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130891, d131067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130892 q = 1) (hb : d131068 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130892, d131068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130892, d131068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130893 q = 1) (hb : d131069 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130893, d131069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130893, d131069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130894 q = 1) (hb : d131070 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130894, d131070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130894, d131070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130895 q = 1) (hb : d131071 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130895, d131071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130895, d131071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44899 (p : Pattern) (ha : d130901 p = 1) (hb : d131077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130896 q = 1) (hb : d131072 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d130896, d131072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44898 q ha hb
    | true =>
      simp only [d130896, d131072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130897 q = 1) (hb : d131073 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130897, d131073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130897, d131073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130898 q = 1) (hb : d131074 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d130898, d131074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130898, d131074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130899 q = 1) (hb : d131075 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d130899, d131075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130899, d131075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130900 q = 1) (hb : d131076 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d130900, d131076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130900, d131076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130901 q = 1) (hb : d131077 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d130901, d131077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130901, d131077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44900 (p : Pattern) (ha : d130907 p = 1) (hb : d131083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130902 q = 1) (hb : d131078 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d130902, d131078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44899 q ha hb
    | true =>
      simp only [d130902, d131078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130903 q = 1) (hb : d131079 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d130903, d131079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130903, d131079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130904 q = 1) (hb : d131080 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d130904, d131080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130904, d131080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130905 q = 1) (hb : d131081 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d130905, d131081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130905, d131081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130906 q = 1) (hb : d131082 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d130906, d131082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130906, d131082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130907 q = 1) (hb : d131083 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d130907, d131083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130907, d131083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44901 (p : Pattern) (ha : d130913 p = 1) (hb : d131089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130908 q = 1) (hb : d131084 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d130908, d131084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44900 q ha hb
    | true =>
      simp only [d130908, d131084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130909 q = 1) (hb : d131085 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d130909, d131085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130909, d131085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130910 q = 1) (hb : d131086 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d130910, d131086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130910, d131086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130911 q = 1) (hb : d131087 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d130911, d131087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130911, d131087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130912 q = 1) (hb : d131088 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d130912, d131088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130912, d131088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130913 q = 1) (hb : d131089 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d130913, d131089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130913, d131089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44902 (p : Pattern) (ha : d130919 p = 1) (hb : d131095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130914 q = 1) (hb : d131090 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d130914, d131090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44901 q ha hb
    | true =>
      simp only [d130914, d131090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130915 q = 1) (hb : d131091 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d130915, d131091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130915, d131091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130916 q = 1) (hb : d131092 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d130916, d131092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130916, d131092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130917 q = 1) (hb : d131093 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d130917, d131093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130917, d131093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130918 q = 1) (hb : d131094 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d130918, d131094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130918, d131094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130919 q = 1) (hb : d131095 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d130919, d131095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130919, d131095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44903 (p : Pattern) (ha : d192717 p = 1) (hb : d192913 p = 1) : d192913 p = 1 := by
  have h0 (q : Pattern) (ha : d192717 q = 1) (hb : d192913 q = 1) : d192913 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro44904 (p : Pattern) (ha : d20477 p = 1) (hb : d130518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20397 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44823 q ha hb
    | true =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20473 q = 1) (hb : d130514 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20473, d130514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20473, d130514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130491 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20474 q = 1) (hb : d130515 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20474, d130515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20474, d130515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20475 q = 1) (hb : d130516 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20475, d130516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20475, d130516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20476 q = 1) (hb : d130517 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20476, d130517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20476, d130517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20477 q = 1) (hb : d130518 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20477, d130518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20477, d130518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44905 (p : Pattern) (ha : d130524 p = 1) (hb : d192722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20478 q = 1) (hb : d130519 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, d130519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, d130519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44904 q ha hb
  have h2 (q : Pattern) (ha : d130520 q = 1) (hb : d192718 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130520, d192718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130520, d192718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130521 q = 1) (hb : d192719 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130521, d192719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130521, d192719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130522 q = 1) (hb : d192720 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130522, d192720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130522, d192720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130523 q = 1) (hb : d192721 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130523, d192721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130523, d192721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130524 q = 1) (hb : d192722 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130524, d192722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130524, d192722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44906 (p : Pattern) (ha : d130548 p = 1) (hb : d192732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130537 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20420 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20420, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44827 q ha hb
    | true =>
      simp only [d20420, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44823 q ha hb
  have h3 (q : Pattern) (ha : d130538 q = 1) (hb : d192728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130538, d192728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130538, d192728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130544 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130545 q = 1) (hb : d192729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130545, d192729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130545, d192729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130546 q = 1) (hb : d192730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130546, d192730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130546, d192730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130547 q = 1) (hb : d192731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130547, d192731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130547, d192731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130548 q = 1) (hb : d192732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130548, d192732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130548, d192732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44907 (p : Pattern) (ha : d130560 p = 1) (hb : d192738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130549 q = 1) (hb : d192733 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130549, d192733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130549, d192733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44906 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130556 q = 1) (hb : d192734 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130556, d192734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130556, d192734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130557 q = 1) (hb : d192735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130557, d192735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130557, d192735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130558 q = 1) (hb : d192736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130558, d192736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130558, d192736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130559 q = 1) (hb : d192737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130559, d192737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130559, d192737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130560 q = 1) (hb : d192738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130560, d192738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130560, d192738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44908 (p : Pattern) (ha : d130566 p = 1) (hb : d192744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130505 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130525 q = 1) (hb : d192723 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130525, d192723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130525, d192723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44905 q ha hb
  have h3 (q : Pattern) (ha : d130526 q = 1) (hb : d192724 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130526, d192724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130526, d192724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130527 q = 1) (hb : d192725 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130527, d192725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130527, d192725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130528 q = 1) (hb : d192726 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130528, d192726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130528, d192726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130529 q = 1) (hb : d192727 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130529, d192727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130529, d192727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130561 q = 1) (hb : d192739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130561, d192739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130561, d192739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44907 q ha hb
  have h8 (q : Pattern) (ha : d130562 q = 1) (hb : d192740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130562, d192740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130562, d192740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130563 q = 1) (hb : d192741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130563, d192741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130563, d192741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130564 q = 1) (hb : d192742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130564, d192742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130564, d192742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130565 q = 1) (hb : d192743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130565, d192743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130565, d192743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130566 q = 1) (hb : d192744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130566, d192744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130566, d192744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro44909 (p : Pattern) (ha : d130600 p = 1) (hb : d192750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130584 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130589 q = 1) (hb : d192745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130589, d192745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44843 q hb ha
    | true =>
      simp only [d130589, d192745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44838 q hb ha
  have h3 (q : Pattern) (ha : d130590 q = 1) (hb : d192746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130590, d192746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130590, d192746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130596 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130597 q = 1) (hb : d192747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130597, d192747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130597, d192747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130598 q = 1) (hb : d192748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130598, d192748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130598, d192748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130599 q = 1) (hb : d192749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130599, d192749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130599, d192749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130600 q = 1) (hb : d192750 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130600, d192750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130600, d192750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44910 (p : Pattern) (ha : d130613 p = 1) (hb : d192756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130601 q = 1) (hb : d192751 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130601, d192751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130601, d192751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44909 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130608 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130609 q = 1) (hb : d192752 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130609, d192752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130609, d192752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130610 q = 1) (hb : d192753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130610, d192753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130610, d192753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130611 q = 1) (hb : d192754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130611, d192754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130611, d192754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130612 q = 1) (hb : d192755 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130612, d192755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130612, d192755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130613 q = 1) (hb : d192756 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130613, d192756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130613, d192756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44911 (p : Pattern) (ha : d130619 p = 1) (hb : d192762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130614 q = 1) (hb : d192757 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130614, d192757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130614, d192757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44910 q ha hb
  have h2 (q : Pattern) (ha : d130615 q = 1) (hb : d192758 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130615, d192758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130615, d192758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130616 q = 1) (hb : d192759 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130616, d192759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130616, d192759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130617 q = 1) (hb : d192760 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130617, d192760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130617, d192760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130618 q = 1) (hb : d192761 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130618, d192761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130618, d192761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130619 q = 1) (hb : d192762 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130619, d192762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130619, d192762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44912 (p : Pattern) (ha : d130654 p = 1) (hb : d192769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130638 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130643 q = 1) (hb : d192764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130643, d192764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44854 q hb ha
    | true =>
      simp only [d130643, d192764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44849 q hb ha
  have h3 (q : Pattern) (ha : d130644 q = 1) (hb : d192765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130644, d192765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130644, d192765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130650 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130651 q = 1) (hb : d192766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130651, d192766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130651, d192766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130652 q = 1) (hb : d192767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130652, d192767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130652, d192767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130653 q = 1) (hb : d192768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130653, d192768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130653, d192768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130654 q = 1) (hb : d192769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130654, d192769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130654, d192769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44913 (p : Pattern) (ha : d130667 p = 1) (hb : d192775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130655 q = 1) (hb : d192770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130655, d192770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130655, d192770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44912 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130662 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130663 q = 1) (hb : d192771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130663, d192771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130663, d192771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130664 q = 1) (hb : d192772 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130664, d192772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130664, d192772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130665 q = 1) (hb : d192773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130665, d192773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130665, d192773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130666 q = 1) (hb : d192774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130666, d192774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130666, d192774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130667 q = 1) (hb : d192775 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130667, d192775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130667, d192775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44914 (p : Pattern) (ha : d130673 p = 1) (hb : d192781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130668 q = 1) (hb : d192776 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130668, d192776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130668, d192776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44913 q ha hb
  have h2 (q : Pattern) (ha : d130669 q = 1) (hb : d192777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130669, d192777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130669, d192777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130670 q = 1) (hb : d192778 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130670, d192778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130670, d192778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130671 q = 1) (hb : d192779 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130671, d192779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130671, d192779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130672 q = 1) (hb : d192780 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130672, d192780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130672, d192780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130673 q = 1) (hb : d192781 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130673, d192781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130673, d192781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44915 (p : Pattern) (ha : d130694 p = 1) (hb : d192784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37965 q ha hb
    | true =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
    | true =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33885 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d127494 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37942 q ha hb
    | true =>
      simp only [d16693, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33858 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d127495 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d127496 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d127497 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d127507 q = 1) (hb : d171139 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127507, d171139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d127507, d171139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h14 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h17 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h21 (q : Pattern) (ha : d9871 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9872 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9873 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d101404 q = 1) (hb : d129539 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101404, d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d101404, d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d130694 q = 1) (hb : d192784 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130694, d192784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130694, d192784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44916 (p : Pattern) (ha : d130700 p = 1) (hb : d192790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130695 q = 1) (hb : d192785 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130695, d192785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44915 q ha hb
    | true =>
      simp only [d130695, d192785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130696 q = 1) (hb : d192786 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130696, d192786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130696, d192786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d130687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44859 q ha hb
    | true =>
      simp only [d20638, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d130688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130697 q = 1) (hb : d192787 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130697, d192787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130697, d192787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130698 q = 1) (hb : d192788 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130698, d192788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130698, d192788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130699 q = 1) (hb : d192789 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130699, d192789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130699, d192789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130700 q = 1) (hb : d192790 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130700, d192790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130700, d192790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro44917 (p : Pattern) (ha : d130719 p = 1) (hb : d192796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130693 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130705 q = 1) (hb : d192791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130705, d192791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44916 q ha hb
    | true =>
      simp only [d130705, d192791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44860 q hb ha
  have h3 (q : Pattern) (ha : d130706 q = 1) (hb : d192792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130706, d192792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130706, d192792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130715 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130716 q = 1) (hb : d192793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130716, d192793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130716, d192793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130717 q = 1) (hb : d192794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130717, d192794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130717, d192794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130718 q = 1) (hb : d192795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130718, d192795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130718, d192795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130719 q = 1) (hb : d192796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130719, d192796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130719, d192796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44918 (p : Pattern) (ha : d130732 p = 1) (hb : d192802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130720 q = 1) (hb : d192797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130720, d192797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130720, d192797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44917 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130728 q = 1) (hb : d192798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130728, d192798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130728, d192798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130729 q = 1) (hb : d192799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130729, d192799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130729, d192799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130730 q = 1) (hb : d192800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130730, d192800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130730, d192800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130731 q = 1) (hb : d192801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130731, d192801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130731, d192801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130732 q = 1) (hb : d192802 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130732, d192802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130732, d192802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44919 (p : Pattern) (ha : d130738 p = 1) (hb : d192808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130733 q = 1) (hb : d192803 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130733, d192803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130733, d192803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44918 q ha hb
  have h2 (q : Pattern) (ha : d130734 q = 1) (hb : d192804 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130734, d192804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130734, d192804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130735 q = 1) (hb : d192805 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130735, d192805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130735, d192805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130736 q = 1) (hb : d192806 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130736, d192806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130736, d192806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130737 q = 1) (hb : d192807 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130737, d192807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130737, d192807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130738 q = 1) (hb : d192808 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130738, d192808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130738, d192808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44920 (p : Pattern) (ha : d130760 p = 1) (hb : d192812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38012 q ha hb
    | true =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
    | true =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33938 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17053 q = 1) (hb : d127787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37989 q ha hb
    | true =>
      simp only [d17053, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33911 q ha hb
  have h9 (q : Pattern) (ha : d17054 q = 1) (hb : d127788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17055 q = 1) (hb : d127789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17056 q = 1) (hb : d127790 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17056, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d127800 q = 1) (hb : d171176 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127800, d171176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d127800, d171176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h14 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h17 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h21 (q : Pattern) (ha : d10165 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10166 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10167 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d101604 q = 1) (hb : d129568 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101604, d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d101604, d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d130760 q = 1) (hb : d192812 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130760, d192812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130760, d192812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44921 (p : Pattern) (ha : d130766 p = 1) (hb : d192818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130761 q = 1) (hb : d192813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130761, d192813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44920 q ha hb
    | true =>
      simp only [d130761, d192813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130762 q = 1) (hb : d192814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130762, d192814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130762, d192814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d130753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44871 q ha hb
    | true =>
      simp only [d20711, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d130754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130763 q = 1) (hb : d192815 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130763, d192815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130763, d192815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130764 q = 1) (hb : d192816 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130764, d192816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130764, d192816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130765 q = 1) (hb : d192817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130765, d192817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130765, d192817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130766 q = 1) (hb : d192818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130766, d192818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130766, d192818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro44922 (p : Pattern) (ha : d130785 p = 1) (hb : d192824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130759 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130771 q = 1) (hb : d192819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130771, d192819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44921 q ha hb
    | true =>
      simp only [d130771, d192819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44872 q hb ha
  have h3 (q : Pattern) (ha : d130772 q = 1) (hb : d192820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130772, d192820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130772, d192820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130781 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130782 q = 1) (hb : d192821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130782, d192821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130782, d192821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130783 q = 1) (hb : d192822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130783, d192822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130783, d192822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130784 q = 1) (hb : d192823 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130784, d192823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130784, d192823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130785 q = 1) (hb : d192824 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130785, d192824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130785, d192824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44923 (p : Pattern) (ha : d130798 p = 1) (hb : d192830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130786 q = 1) (hb : d192825 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130786, d192825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130786, d192825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44922 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130794 q = 1) (hb : d192826 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130794, d192826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130794, d192826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130795 q = 1) (hb : d192827 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130795, d192827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130795, d192827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130796 q = 1) (hb : d192828 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130796, d192828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130796, d192828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130797 q = 1) (hb : d192829 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130797, d192829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130797, d192829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130798 q = 1) (hb : d192830 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130798, d192830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130798, d192830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44924 (p : Pattern) (ha : d130804 p = 1) (hb : d192836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130799 q = 1) (hb : d192831 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130799, d192831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130799, d192831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44923 q ha hb
  have h2 (q : Pattern) (ha : d130800 q = 1) (hb : d192832 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130800, d192832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130800, d192832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130801 q = 1) (hb : d192833 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130801, d192833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130801, d192833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130802 q = 1) (hb : d192834 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130802, d192834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130802, d192834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130803 q = 1) (hb : d192835 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130803, d192835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130803, d192835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130804 q = 1) (hb : d192836 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130804, d192836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130804, d192836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44925 (p : Pattern) (ha : d130827 p = 1) (hb : d192841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38059 q ha hb
    | true =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
    | true =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33991 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17417 q = 1) (hb : d128079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro38036 q ha hb
    | true =>
      simp only [d17417, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33964 q ha hb
  have h9 (q : Pattern) (ha : d17418 q = 1) (hb : d128080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17419 q = 1) (hb : d128081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17420 q = 1) (hb : d128082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17420, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128092 q = 1) (hb : d171214 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128092, d171214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128092, d171214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h14 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h17 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h21 (q : Pattern) (ha : d10442 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10443 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10444 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d101775 q = 1) (hb : d129598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101775, d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d101775, d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d130827 q = 1) (hb : d192841 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130827, d192841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130827, d192841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro44926 (p : Pattern) (ha : d130833 p = 1) (hb : d192847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130828 q = 1) (hb : d192842 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130828, d192842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44925 q ha hb
    | true =>
      simp only [d130828, d192842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130829 q = 1) (hb : d192843 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130829, d192843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130829, d192843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d130820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44883 q ha hb
    | true =>
      simp only [d20785, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d130821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130830 q = 1) (hb : d192844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130830, d192844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130830, d192844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130831 q = 1) (hb : d192845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130831, d192845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130831, d192845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130832 q = 1) (hb : d192846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130832, d192846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130832, d192846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130833 q = 1) (hb : d192847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130833, d192847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130833, d192847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro44927 (p : Pattern) (ha : d130852 p = 1) (hb : d192853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130838 q = 1) (hb : d192848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130838, d192848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44926 q ha hb
    | true =>
      simp only [d130838, d192848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44884 q hb ha
  have h3 (q : Pattern) (ha : d130839 q = 1) (hb : d192849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130839, d192849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130839, d192849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130848 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130849 q = 1) (hb : d192850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130849, d192850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130849, d192850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130850 q = 1) (hb : d192851 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130850, d192851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130850, d192851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130851 q = 1) (hb : d192852 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130851, d192852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130851, d192852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130852 q = 1) (hb : d192853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130852, d192853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130852, d192853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44928 (p : Pattern) (ha : d130865 p = 1) (hb : d192859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130853 q = 1) (hb : d192854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130853, d192854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130853, d192854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44927 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130860 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130861 q = 1) (hb : d192855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130861, d192855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130861, d192855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130862 q = 1) (hb : d192856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130862, d192856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130862, d192856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130863 q = 1) (hb : d192857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130863, d192857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130863, d192857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130864 q = 1) (hb : d192858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130864, d192858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130864, d192858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130865 q = 1) (hb : d192859 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130865, d192859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130865, d192859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44929 (p : Pattern) (ha : d130871 p = 1) (hb : d192865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130866 q = 1) (hb : d192860 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130866, d192860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130866, d192860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44928 q ha hb
  have h2 (q : Pattern) (ha : d130867 q = 1) (hb : d192861 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130867, d192861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130867, d192861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130868 q = 1) (hb : d192862 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130868, d192862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130868, d192862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130869 q = 1) (hb : d192863 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130869, d192863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130869, d192863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130870 q = 1) (hb : d192864 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130870, d192864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130870, d192864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130871 q = 1) (hb : d192865 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130871, d192865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130871, d192865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44930 (p : Pattern) (ha : d130877 p = 1) (hb : d192871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130620 q = 1) (hb : d192763 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130620, d192763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44908 q ha hb
    | true =>
      simp only [d130620, d192763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44911 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130674 q = 1) (hb : d192782 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130674, d192782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130674, d192782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44914 q ha hb
  have h3 (q : Pattern) (ha : d130675 q = 1) (hb : d192783 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130675, d192783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130675, d192783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130739 q = 1) (hb : d192809 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130739, d192809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130739, d192809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44919 q ha hb
  have h5 (q : Pattern) (ha : d130740 q = 1) (hb : d192810 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130740, d192810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130740, d192810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130741 q = 1) (hb : d192811 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130741, d192811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130741, d192811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130805 q = 1) (hb : d192837 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130805, d192837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130805, d192837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44924 q ha hb
  have h8 (q : Pattern) (ha : d130806 q = 1) (hb : d192838 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130806, d192838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130806, d192838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130807 q = 1) (hb : d192839 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130807, d192839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130807, d192839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130808 q = 1) (hb : d192840 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130808, d192840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130808, d192840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130872 q = 1) (hb : d192866 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130872, d192866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130872, d192866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44929 q ha hb
  have h12 (q : Pattern) (ha : d130873 q = 1) (hb : d192867 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130873, d192867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130873, d192867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130874 q = 1) (hb : d192868 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130874, d192868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130874, d192868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130875 q = 1) (hb : d192869 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130875, d192869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130875, d192869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130876 q = 1) (hb : d192870 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130876, d192870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130876, d192870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130877 q = 1) (hb : d192871 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130877, d192871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130877, d192871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro44931 (p : Pattern) (ha : d130883 p = 1) (hb : d192877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130878 q = 1) (hb : d192872 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130878, d192872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44930 q ha hb
    | true =>
      simp only [d130878, d192872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130879 q = 1) (hb : d192873 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130879, d192873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130879, d192873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130880 q = 1) (hb : d192874 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130880, d192874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130880, d192874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130881 q = 1) (hb : d192875 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130881, d192875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130881, d192875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130882 q = 1) (hb : d192876 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130882, d192876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130882, d192876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130883 q = 1) (hb : d192877 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130883, d192877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130883, d192877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44932 (p : Pattern) (ha : d130889 p = 1) (hb : d192883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130884 q = 1) (hb : d192878 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130884, d192878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44931 q ha hb
    | true =>
      simp only [d130884, d192878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130885 q = 1) (hb : d192879 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130885, d192879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130885, d192879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130886 q = 1) (hb : d192880 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130886, d192880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130886, d192880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130887 q = 1) (hb : d192881 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130887, d192881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130887, d192881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130888 q = 1) (hb : d192882 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130888, d192882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130888, d192882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130889 q = 1) (hb : d192883 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130889, d192883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130889, d192883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44933 (p : Pattern) (ha : d130895 p = 1) (hb : d192889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130890 q = 1) (hb : d192884 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130890, d192884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44932 q ha hb
    | true =>
      simp only [d130890, d192884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130891 q = 1) (hb : d192885 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130891, d192885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130891, d192885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130892 q = 1) (hb : d192886 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130892, d192886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130892, d192886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130893 q = 1) (hb : d192887 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130893, d192887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130893, d192887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130894 q = 1) (hb : d192888 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130894, d192888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130894, d192888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130895 q = 1) (hb : d192889 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130895, d192889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130895, d192889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44934 (p : Pattern) (ha : d130901 p = 1) (hb : d192895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130896 q = 1) (hb : d192890 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d130896, d192890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44933 q ha hb
    | true =>
      simp only [d130896, d192890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130897 q = 1) (hb : d192891 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130897, d192891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130897, d192891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130898 q = 1) (hb : d192892 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d130898, d192892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130898, d192892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130899 q = 1) (hb : d192893 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d130899, d192893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130899, d192893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130900 q = 1) (hb : d192894 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d130900, d192894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130900, d192894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130901 q = 1) (hb : d192895 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d130901, d192895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130901, d192895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44935 (p : Pattern) (ha : d130907 p = 1) (hb : d192901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130902 q = 1) (hb : d192896 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d130902, d192896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44934 q ha hb
    | true =>
      simp only [d130902, d192896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130903 q = 1) (hb : d192897 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d130903, d192897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130903, d192897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130904 q = 1) (hb : d192898 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d130904, d192898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130904, d192898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130905 q = 1) (hb : d192899 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d130905, d192899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130905, d192899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130906 q = 1) (hb : d192900 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d130906, d192900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130906, d192900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130907 q = 1) (hb : d192901 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d130907, d192901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130907, d192901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44936 (p : Pattern) (ha : d130913 p = 1) (hb : d192907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130908 q = 1) (hb : d192902 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d130908, d192902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44935 q ha hb
    | true =>
      simp only [d130908, d192902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130909 q = 1) (hb : d192903 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d130909, d192903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130909, d192903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130910 q = 1) (hb : d192904 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d130910, d192904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130910, d192904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130911 q = 1) (hb : d192905 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d130911, d192905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130911, d192905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130912 q = 1) (hb : d192906 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d130912, d192906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130912, d192906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130913 q = 1) (hb : d192907 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d130913, d192907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130913, d192907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44937 (p : Pattern) (ha : d130919 p = 1) (hb : d192913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130914 q = 1) (hb : d192908 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d130914, d192908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44936 q ha hb
    | true =>
      simp only [d130914, d192908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130915 q = 1) (hb : d192909 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d130915, d192909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130915, d192909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130916 q = 1) (hb : d192910 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d130916, d192910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130916, d192910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130917 q = 1) (hb : d192911 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d130917, d192911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130917, d192911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130918 q = 1) (hb : d192912 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d130918, d192912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130918, d192912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130919 q = 1) (hb : d192913 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d130919, d192913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130919, d192913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro44938 (p : Pattern) (ha : d20477 p = 1) (hb : d130924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20397 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20473 q = 1) (hb : d130920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20473, d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20473, d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20398 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20474 q = 1) (hb : d130921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20474, d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20474, d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20475 q = 1) (hb : d130922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20475, d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20475, d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20476 q = 1) (hb : d130923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20476, d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20476, d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20477 q = 1) (hb : d130924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20477, d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20477, d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44939 (p : Pattern) (ha : d130930 p = 1) (hb : d192722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20478 q = 1) (hb : d130925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44938 q ha hb
  have h2 (q : Pattern) (ha : d130926 q = 1) (hb : d192718 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130926, d192718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130926, d192718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130927 q = 1) (hb : d192719 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130927, d192719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130927, d192719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130928 q = 1) (hb : d192720 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130928, d192720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130928, d192720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130929 q = 1) (hb : d192721 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130929, d192721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130929, d192721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130930 q = 1) (hb : d192722 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130930, d192722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130930, d192722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44940 (p : Pattern) (ha : d130940 p = 1) (hb : d192732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20420 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130936 q = 1) (hb : d192728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130936, d192728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130936, d192728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130937 q = 1) (hb : d192729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130937, d192729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130937, d192729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130938 q = 1) (hb : d192730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130938, d192730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130938, d192730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130939 q = 1) (hb : d192731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130939, d192731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130939, d192731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130940 q = 1) (hb : d192732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130940, d192732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130940, d192732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44941 (p : Pattern) (ha : d130946 p = 1) (hb : d192738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130941 q = 1) (hb : d192733 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130941, d192733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130941, d192733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44940 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130942 q = 1) (hb : d192734 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130942, d192734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130942, d192734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130943 q = 1) (hb : d192735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130943, d192735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130943, d192735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130944 q = 1) (hb : d192736 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130944, d192736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130944, d192736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130945 q = 1) (hb : d192737 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130945, d192737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130945, d192737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130946 q = 1) (hb : d192738 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130946, d192738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130946, d192738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44942 (p : Pattern) (ha : d130952 p = 1) (hb : d192744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130931 q = 1) (hb : d192723 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130931, d192723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130931, d192723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44939 q ha hb
  have h3 (q : Pattern) (ha : d130932 q = 1) (hb : d192724 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130932, d192724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130932, d192724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130933 q = 1) (hb : d192725 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130933, d192725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130933, d192725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130934 q = 1) (hb : d192726 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130934, d192726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130934, d192726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130935 q = 1) (hb : d192727 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130935, d192727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130935, d192727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130947 q = 1) (hb : d192739 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130947, d192739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130947, d192739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44941 q ha hb
  have h8 (q : Pattern) (ha : d130948 q = 1) (hb : d192740 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130948, d192740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130948, d192740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130949 q = 1) (hb : d192741 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130949, d192741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130949, d192741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130950 q = 1) (hb : d192742 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130950, d192742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130950, d192742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130951 q = 1) (hb : d192743 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130951, d192743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130951, d192743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130952 q = 1) (hb : d192744 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130952, d192744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130952, d192744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro44943 (p : Pattern) (ha : d130957 p = 1) (hb : d192750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20507 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192745 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130953 q = 1) (hb : d192746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130953, d192746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130953, d192746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20529 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130954 q = 1) (hb : d192747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130954, d192747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130954, d192747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130955 q = 1) (hb : d192748 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130955, d192748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130955, d192748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130956 q = 1) (hb : d192749 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130956, d192749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130956, d192749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130957 q = 1) (hb : d192750 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130957, d192750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130957, d192750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44944 (p : Pattern) (ha : d130963 p = 1) (hb : d192756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130958 q = 1) (hb : d192751 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130958, d192751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130958, d192751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44943 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20545 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130959 q = 1) (hb : d192752 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130959, d192752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130959, d192752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130960 q = 1) (hb : d192753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130960, d192753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130960, d192753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130961 q = 1) (hb : d192754 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130961, d192754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130961, d192754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130962 q = 1) (hb : d192755 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130962, d192755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130962, d192755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130963 q = 1) (hb : d192756 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130963, d192756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130963, d192756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44945 (p : Pattern) (ha : d130969 p = 1) (hb : d192762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130964 q = 1) (hb : d192757 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130964, d192757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130964, d192757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44944 q ha hb
  have h2 (q : Pattern) (ha : d130965 q = 1) (hb : d192758 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130965, d192758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130965, d192758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130966 q = 1) (hb : d192759 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130966, d192759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130966, d192759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130967 q = 1) (hb : d192760 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130967, d192760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130967, d192760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130968 q = 1) (hb : d192761 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130968, d192761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130968, d192761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130969 q = 1) (hb : d192762 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130969, d192762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130969, d192762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44946 (p : Pattern) (ha : d130975 p = 1) (hb : d192769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130971 q = 1) (hb : d192765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130971, d192765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130971, d192765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20597 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130972 q = 1) (hb : d192766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130972, d192766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130972, d192766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130973 q = 1) (hb : d192767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130973, d192767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130973, d192767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130974 q = 1) (hb : d192768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130974, d192768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130974, d192768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130975 q = 1) (hb : d192769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130975, d192769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130975, d192769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44947 (p : Pattern) (ha : d130981 p = 1) (hb : d192775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130976 q = 1) (hb : d192770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130976, d192770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130976, d192770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44946 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20613 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130977 q = 1) (hb : d192771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130977, d192771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130977, d192771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130978 q = 1) (hb : d192772 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130978, d192772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130978, d192772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130979 q = 1) (hb : d192773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130979, d192773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130979, d192773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130980 q = 1) (hb : d192774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130980, d192774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130980, d192774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130981 q = 1) (hb : d192775 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130981, d192775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130981, d192775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44948 (p : Pattern) (ha : d130987 p = 1) (hb : d192781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130982 q = 1) (hb : d192776 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130982, d192776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130982, d192776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44947 q ha hb
  have h2 (q : Pattern) (ha : d130983 q = 1) (hb : d192777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130983, d192777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130983, d192777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130984 q = 1) (hb : d192778 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130984, d192778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130984, d192778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130985 q = 1) (hb : d192779 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130985, d192779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130985, d192779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130986 q = 1) (hb : d192780 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130986, d192780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130986, d192780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130987 q = 1) (hb : d192781 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130987, d192781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130987, d192781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44949 (p : Pattern) (ha : d130994 p = 1) (hb : d192796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130990 q = 1) (hb : d192792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130990, d192792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130990, d192792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20669 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130991 q = 1) (hb : d192793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130991, d192793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130991, d192793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130992 q = 1) (hb : d192794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130992, d192794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130992, d192794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130993 q = 1) (hb : d192795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130993, d192795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130993, d192795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130994 q = 1) (hb : d192796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130994, d192796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130994, d192796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44950 (p : Pattern) (ha : d131000 p = 1) (hb : d192802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130995 q = 1) (hb : d192797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130995, d192797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130995, d192797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44949 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20685 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130996 q = 1) (hb : d192798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130996, d192798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130996, d192798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130997 q = 1) (hb : d192799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130997, d192799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130997, d192799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130998 q = 1) (hb : d192800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130998, d192800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130998, d192800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130999 q = 1) (hb : d192801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130999, d192801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130999, d192801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131000 q = 1) (hb : d192802 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131000, d192802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131000, d192802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44951 (p : Pattern) (ha : d131006 p = 1) (hb : d192808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131001 q = 1) (hb : d192803 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131001, d192803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131001, d192803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44950 q ha hb
  have h2 (q : Pattern) (ha : d131002 q = 1) (hb : d192804 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131002, d192804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131002, d192804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131003 q = 1) (hb : d192805 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131003, d192805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131003, d192805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131004 q = 1) (hb : d192806 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131004, d192806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131004, d192806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131005 q = 1) (hb : d192807 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131005, d192807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131005, d192807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131006 q = 1) (hb : d192808 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131006, d192808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131006, d192808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44952 (p : Pattern) (ha : d131014 p = 1) (hb : d192824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131010 q = 1) (hb : d192820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131010, d192820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131010, d192820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20742 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131011 q = 1) (hb : d192821 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131011, d192821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131011, d192821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131012 q = 1) (hb : d192822 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131012, d192822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131012, d192822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131013 q = 1) (hb : d192823 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131013, d192823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131013, d192823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131014 q = 1) (hb : d192824 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131014, d192824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131014, d192824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44953 (p : Pattern) (ha : d131020 p = 1) (hb : d192830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131015 q = 1) (hb : d192825 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131015, d192825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131015, d192825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44952 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131016 q = 1) (hb : d192826 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131016, d192826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131016, d192826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131017 q = 1) (hb : d192827 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131017, d192827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131017, d192827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131018 q = 1) (hb : d192828 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131018, d192828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131018, d192828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131019 q = 1) (hb : d192829 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131019, d192829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131019, d192829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131020 q = 1) (hb : d192830 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131020, d192830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131020, d192830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44954 (p : Pattern) (ha : d131026 p = 1) (hb : d192836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131021 q = 1) (hb : d192831 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131021, d192831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131021, d192831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44953 q ha hb
  have h2 (q : Pattern) (ha : d131022 q = 1) (hb : d192832 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131022, d192832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131022, d192832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131023 q = 1) (hb : d192833 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131023, d192833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131023, d192833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131024 q = 1) (hb : d192834 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131024, d192834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131024, d192834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131025 q = 1) (hb : d192835 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131025, d192835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131025, d192835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131026 q = 1) (hb : d192836 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131026, d192836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131026, d192836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44955 (p : Pattern) (ha : d131035 p = 1) (hb : d192853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d192848 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131031 q = 1) (hb : d192849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131031, d192849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131031, d192849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131032 q = 1) (hb : d192850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131032, d192850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131032, d192850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131033 q = 1) (hb : d192851 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131033, d192851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131033, d192851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131034 q = 1) (hb : d192852 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131034, d192852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131034, d192852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131035 q = 1) (hb : d192853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131035, d192853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131035, d192853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44956 (p : Pattern) (ha : d131041 p = 1) (hb : d192859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131036 q = 1) (hb : d192854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131036, d192854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131036, d192854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44955 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20832 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131037 q = 1) (hb : d192855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131037, d192855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131037, d192855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131038 q = 1) (hb : d192856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131038, d192856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131038, d192856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131039 q = 1) (hb : d192857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131039, d192857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131039, d192857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131040 q = 1) (hb : d192858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131040, d192858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131040, d192858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131041 q = 1) (hb : d192859 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131041, d192859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131041, d192859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44957 (p : Pattern) (ha : d131047 p = 1) (hb : d192865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131042 q = 1) (hb : d192860 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131042, d192860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131042, d192860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44956 q ha hb
  have h2 (q : Pattern) (ha : d131043 q = 1) (hb : d192861 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131043, d192861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131043, d192861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131044 q = 1) (hb : d192862 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131044, d192862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131044, d192862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131045 q = 1) (hb : d192863 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131045, d192863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131045, d192863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131046 q = 1) (hb : d192864 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131046, d192864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131046, d192864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131047 q = 1) (hb : d192865 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131047, d192865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131047, d192865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44958 (p : Pattern) (ha : d131053 p = 1) (hb : d192871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130970 q = 1) (hb : d192763 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130970, d192763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44942 q ha hb
    | true =>
      simp only [d130970, d192763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44945 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130988 q = 1) (hb : d192782 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130988, d192782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130988, d192782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44948 q ha hb
  have h3 (q : Pattern) (ha : d130989 q = 1) (hb : d192783 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130989, d192783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130989, d192783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131007 q = 1) (hb : d192809 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131007, d192809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131007, d192809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44951 q ha hb
  have h5 (q : Pattern) (ha : d131008 q = 1) (hb : d192810 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131008, d192810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131008, d192810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131009 q = 1) (hb : d192811 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131009, d192811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131009, d192811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131027 q = 1) (hb : d192837 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131027, d192837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131027, d192837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44954 q ha hb
  have h8 (q : Pattern) (ha : d131028 q = 1) (hb : d192838 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131028, d192838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131028, d192838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131029 q = 1) (hb : d192839 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131029, d192839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131029, d192839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131030 q = 1) (hb : d192840 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131030, d192840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131030, d192840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131048 q = 1) (hb : d192866 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131048, d192866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131048, d192866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44957 q ha hb
  have h12 (q : Pattern) (ha : d131049 q = 1) (hb : d192867 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131049, d192867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131049, d192867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131050 q = 1) (hb : d192868 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131050, d192868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131050, d192868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131051 q = 1) (hb : d192869 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131051, d192869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131051, d192869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131052 q = 1) (hb : d192870 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131052, d192870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131052, d192870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131053 q = 1) (hb : d192871 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131053, d192871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131053, d192871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro44959 (p : Pattern) (ha : d131059 p = 1) (hb : d192877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131054 q = 1) (hb : d192872 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131054, d192872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44958 q ha hb
    | true =>
      simp only [d131054, d192872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131055 q = 1) (hb : d192873 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131055, d192873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131055, d192873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131056 q = 1) (hb : d192874 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131056, d192874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131056, d192874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131057 q = 1) (hb : d192875 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131057, d192875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131057, d192875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131058 q = 1) (hb : d192876 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131058, d192876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131058, d192876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131059 q = 1) (hb : d192877 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131059, d192877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131059, d192877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44960 (p : Pattern) (ha : d131065 p = 1) (hb : d192883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131060 q = 1) (hb : d192878 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131060, d192878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44959 q ha hb
    | true =>
      simp only [d131060, d192878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131061 q = 1) (hb : d192879 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131061, d192879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131061, d192879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131062 q = 1) (hb : d192880 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131062, d192880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131062, d192880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131063 q = 1) (hb : d192881 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131063, d192881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131063, d192881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131064 q = 1) (hb : d192882 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131064, d192882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131064, d192882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131065 q = 1) (hb : d192883 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131065, d192883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131065, d192883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44961 (p : Pattern) (ha : d131071 p = 1) (hb : d192889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131066 q = 1) (hb : d192884 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131066, d192884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44960 q ha hb
    | true =>
      simp only [d131066, d192884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131067 q = 1) (hb : d192885 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131067, d192885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131067, d192885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131068 q = 1) (hb : d192886 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131068, d192886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131068, d192886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131069 q = 1) (hb : d192887 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131069, d192887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131069, d192887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131070 q = 1) (hb : d192888 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131070, d192888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131070, d192888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131071 q = 1) (hb : d192889 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131071, d192889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131071, d192889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44962 (p : Pattern) (ha : d131077 p = 1) (hb : d192895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131072 q = 1) (hb : d192890 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131072, d192890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44961 q ha hb
    | true =>
      simp only [d131072, d192890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131073 q = 1) (hb : d192891 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131073, d192891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131073, d192891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131074 q = 1) (hb : d192892 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131074, d192892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131074, d192892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131075 q = 1) (hb : d192893 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131075, d192893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131075, d192893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131076 q = 1) (hb : d192894 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131076, d192894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131076, d192894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131077 q = 1) (hb : d192895 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131077, d192895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131077, d192895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44963 (p : Pattern) (ha : d131083 p = 1) (hb : d192901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131078 q = 1) (hb : d192896 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131078, d192896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44962 q ha hb
    | true =>
      simp only [d131078, d192896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131079 q = 1) (hb : d192897 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131079, d192897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131079, d192897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131080 q = 1) (hb : d192898 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131080, d192898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131080, d192898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131081 q = 1) (hb : d192899 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131081, d192899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131081, d192899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131082 q = 1) (hb : d192900 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131082, d192900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131082, d192900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131083 q = 1) (hb : d192901 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131083, d192901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131083, d192901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44964 (p : Pattern) (ha : d131089 p = 1) (hb : d192907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131084 q = 1) (hb : d192902 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131084, d192902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44963 q ha hb
    | true =>
      simp only [d131084, d192902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131085 q = 1) (hb : d192903 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131085, d192903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131085, d192903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131086 q = 1) (hb : d192904 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131086, d192904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131086, d192904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131087 q = 1) (hb : d192905 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131087, d192905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131087, d192905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131088 q = 1) (hb : d192906 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131088, d192906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131088, d192906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131089 q = 1) (hb : d192907 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131089, d192907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131089, d192907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44965 (p : Pattern) (ha : d131095 p = 1) (hb : d192913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131090 q = 1) (hb : d192908 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131090, d192908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44964 q ha hb
    | true =>
      simp only [d131090, d192908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131091 q = 1) (hb : d192909 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131091, d192909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131091, d192909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131092 q = 1) (hb : d192910 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131092, d192910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131092, d192910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131093 q = 1) (hb : d192911 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131093, d192911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131093, d192911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131094 q = 1) (hb : d192912 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131094, d192912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131094, d192912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131095 q = 1) (hb : d192913 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131095, d192913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131095, d192913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44966 (p : Pattern) (ha : d71 p = 1) (hb : d102052 p = 1) : d9296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d66 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d25 q = 1) (hb : d102052 q = 1) : d25 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67 q = 1) (hb : d102052 q = 1) : d9292 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26 q = 1) (hb : d102052 q = 1) : d26 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d68 q = 1) (hb : d102052 q = 1) : d9293 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d9293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68, d9293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d69 q = 1) (hb : d102052 q = 1) : d9294 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d9294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69, d9294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d102052 q = 1) : d9295 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d9295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70, d9295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d71 q = 1) (hb : d102052 q = 1) : d9296 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, d9296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71, d9296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro44967 (p : Pattern) (ha : d20390 p = 1) (hb : d102052 p = 1) : d19742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d72 q = 1) (hb : d102052 q = 1) : d9297 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44966 q ha hb
    | true =>
      simp only [d72, d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d73 q = 1) (hb : d102052 q = 1) : d19738 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74 q = 1) (hb : d102052 q = 1) : d19739 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d102052 q = 1) : d19740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d19740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d75, d19740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d102052 q = 1) : d19741 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, d19741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, d19741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9301 q = 1) (hb : d102052 q = 1) : d9301 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20390 q = 1) (hb : d102052 q = 1) : d19742 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20390, d19742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20390, d19742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44968 (p : Pattern) (ha : d20396 p = 1) (hb : d102052 p = 1) : d19748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20391 q = 1) (hb : d102052 q = 1) : d19743 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20391, d19743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44967 q ha hb
    | true =>
      simp only [d20391, d19743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20392 q = 1) (hb : d102052 q = 1) : d19744 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20392, d19744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20392, d19744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20393 q = 1) (hb : d102052 q = 1) : d19745 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20393, d19745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20393, d19745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20394 q = 1) (hb : d102052 q = 1) : d19746 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20394, d19746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20394, d19746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20395 q = 1) (hb : d102052 q = 1) : d19747 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20395, d19747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20395, d19747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20396 q = 1) (hb : d102052 q = 1) : d19748 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20396, d19748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20396, d19748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44969 (p : Pattern) (ha : d20402 p = 1) (hb : d102052 p = 1) : d19754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20397 q = 1) (hb : d102052 q = 1) : d19749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d19749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44968 q ha hb
    | true =>
      simp only [d20397, d19749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20398 q = 1) (hb : d102052 q = 1) : d19750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20398, d19750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20398, d19750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20399 q = 1) (hb : d102052 q = 1) : d19751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20399, d19751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20399, d19751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20400 q = 1) (hb : d102052 q = 1) : d19752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20400, d19752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20400, d19752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20401 q = 1) (hb : d102052 q = 1) : d19753 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20401, d19753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20401, d19753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20402 q = 1) (hb : d102052 q = 1) : d19754 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20402, d19754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20402, d19754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44970 (p : Pattern) (ha : d20408 p = 1) (hb : d102052 p = 1) : d19760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20403 q = 1) (hb : d102052 q = 1) : d19755 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20403, d19755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20403, d19755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44969 q ha hb
  have h2 (q : Pattern) (ha : d20404 q = 1) (hb : d102052 q = 1) : d19756 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20404, d19756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20404, d19756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20405 q = 1) (hb : d102052 q = 1) : d19757 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20405, d19757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20405, d19757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20406 q = 1) (hb : d102052 q = 1) : d19758 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20406, d19758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20406, d19758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20407 q = 1) (hb : d102052 q = 1) : d19759 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20407, d19759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20407, d19759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20408 q = 1) (hb : d102052 q = 1) : d19760 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20408, d19760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20408, d19760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44971 (p : Pattern) (ha : d231 p = 1) (hb : d102052 p = 1) : d9329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d138 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d226 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d139 q = 1) (hb : d102052 q = 1) : d139 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d227 q = 1) (hb : d102052 q = 1) : d9325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d227, d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140 q = 1) (hb : d102052 q = 1) : d140 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d228 q = 1) (hb : d102052 q = 1) : d9326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d9326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d228, d9326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d229 q = 1) (hb : d102052 q = 1) : d9327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d9327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d229, d9327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d66 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d25 q = 1) (hb : d102052 q = 1) : d25 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d67 q = 1) (hb : d102052 q = 1) : d9292 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26 q = 1) (hb : d102052 q = 1) : d26 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d68 q = 1) (hb : d102052 q = 1) : d9293 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d9293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68, d9293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69 q = 1) (hb : d102052 q = 1) : d9294 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d9294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d69, d9294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d230 q = 1) (hb : d102052 q = 1) : d9328 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d9328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d230, d9328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d70 q = 1) (hb : d102052 q = 1) : d9295 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d9295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70, d9295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d231 q = 1) (hb : d102052 q = 1) : d9329 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d9329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d231, d9329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro44972 (p : Pattern) (ha : d20413 p = 1) (hb : d102052 p = 1) : d19769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d102052 q = 1) : d9330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44971 q ha hb
    | true =>
      simp only [d232, d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44966 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d102052 q = 1) : d19765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d102052 q = 1) : d19766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d102052 q = 1) : d9297 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44966 q ha hb
    | true =>
      simp only [d72, d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d102052 q = 1) : d19738 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d102052 q = 1) : d19739 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d235 q = 1) (hb : d102052 q = 1) : d19767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d19767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d235, d19767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d102052 q = 1) : d19740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d19740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d19740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d236 q = 1) (hb : d102052 q = 1) : d19768 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d19768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d236, d19768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9334 q = 1) (hb : d102052 q = 1) : d9334 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d20413 q = 1) (hb : d102052 q = 1) : d19769 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20413, d19769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20413, d19769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44973 (p : Pattern) (ha : d20419 p = 1) (hb : d102052 p = 1) : d19775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20414 q = 1) (hb : d102052 q = 1) : d19770 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d19770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44972 q ha hb
    | true =>
      simp only [d20414, d19770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20415 q = 1) (hb : d102052 q = 1) : d19771 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d19771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, d19771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20391 q = 1) (hb : d102052 q = 1) : d19743 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20391, d19743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44967 q ha hb
    | true =>
      simp only [d20391, d19743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20392 q = 1) (hb : d102052 q = 1) : d19744 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20392, d19744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20392, d19744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20416 q = 1) (hb : d102052 q = 1) : d19772 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20416, d19772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20416, d19772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20417 q = 1) (hb : d102052 q = 1) : d19773 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20417, d19773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20417, d19773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20418 q = 1) (hb : d102052 q = 1) : d19774 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20418, d19774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20418, d19774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20419 q = 1) (hb : d102052 q = 1) : d19775 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20419, d19775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20419, d19775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44974 (p : Pattern) (ha : d102052 p = 1) (hb : d130924 p = 1) : d130215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20420 q = 1) (hb : d102052 q = 1) : d19776 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20420, d19776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44973 q ha hb
    | true =>
      simp only [d20420, d19776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44968 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d130920 q = 1) : d130211 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130920, d130211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130920, d130211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20397 q = 1) (hb : d102052 q = 1) : d19749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d19749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44968 q ha hb
    | true =>
      simp only [d20397, d19749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20398 q = 1) (hb : d102052 q = 1) : d19750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20398, d19750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20398, d19750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130921 q = 1) : d130212 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130921, d130212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130921, d130212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130922 q = 1) : d130213 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130922, d130213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130922, d130213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d130923 q = 1) : d130214 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130923, d130214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130923, d130214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d130924 q = 1) : d130215 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130924, d130215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130924, d130215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44975 (p : Pattern) (ha : d102052 p = 1) (hb : d130930 p = 1) : d130221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d130925 q = 1) : d130216 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130925, d130216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130925, d130216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44974 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d130926 q = 1) : d130217 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130926, d130217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130926, d130217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d130927 q = 1) : d130218 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130927, d130218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130927, d130218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d130928 q = 1) : d130219 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130928, d130219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130928, d130219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130929 q = 1) : d130220 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130929, d130220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130929, d130220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130930 q = 1) : d130221 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130930, d130221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130930, d130221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44976 (p : Pattern) (ha : d20477 p = 1) (hb : d102052 p = 1) : d19845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20397 q = 1) (hb : d102052 q = 1) : d19749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d19749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44968 q ha hb
    | true =>
      simp only [d20397, d19749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20473 q = 1) (hb : d102052 q = 1) : d19841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20473, d19841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20473, d19841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20474 q = 1) (hb : d102052 q = 1) : d19842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20474, d19842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20474, d19842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20475 q = 1) (hb : d102052 q = 1) : d19843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20475, d19843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20475, d19843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20476 q = 1) (hb : d102052 q = 1) : d19844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20476, d19844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20476, d19844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20477 q = 1) (hb : d102052 q = 1) : d19845 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20477, d19845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20477, d19845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44977 (p : Pattern) (ha : d16004 p = 1) (hb : d102052 p = 1) : d9388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d412 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d319 q = 1) (hb : d102052 q = 1) : d319 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d413 q = 1) (hb : d102052 q = 1) : d9377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d413, d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320 q = 1) (hb : d102052 q = 1) : d320 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d414 q = 1) (hb : d102052 q = 1) : d9378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d9378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d414, d9378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d415 q = 1) (hb : d102052 q = 1) : d9379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d9379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d415, d9379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d138 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d226 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d139 q = 1) (hb : d102052 q = 1) : d139 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d227 q = 1) (hb : d102052 q = 1) : d9325 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d227, d9325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d140 q = 1) (hb : d102052 q = 1) : d140 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d228 q = 1) (hb : d102052 q = 1) : d9326 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d9326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d228, d9326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d229 q = 1) (hb : d102052 q = 1) : d9327 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d9327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d229, d9327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d416 q = 1) (hb : d102052 q = 1) : d9380 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d9380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d416, d9380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d9381 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12599 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d9382 q = 1) (hb : d102052 q = 1) : d9382 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d12600 q = 1) (hb : d102052 q = 1) : d9383 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12600, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9384 q = 1) (hb : d102052 q = 1) : d9384 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d12601 q = 1) (hb : d102052 q = 1) : d9385 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d9385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12601, d9385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d12602 q = 1) (hb : d102052 q = 1) : d9386 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d9386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12602, d9386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d24 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d66 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d25 q = 1) (hb : d102052 q = 1) : d25 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d67 q = 1) (hb : d102052 q = 1) : d9292 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d67, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d26 q = 1) (hb : d102052 q = 1) : d26 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d68 q = 1) (hb : d102052 q = 1) : d9293 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d9293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d68, d9293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d69 q = 1) (hb : d102052 q = 1) : d9294 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d9294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d69, d9294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h31 (q : Pattern) (ha : d12603 q = 1) (hb : d102052 q = 1) : d9387 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d9387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d12603, d9387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d16004 q = 1) (hb : d102052 q = 1) : d9388 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d9388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16004, d9388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  exact h32 p ha hb
theorem andIntro44978 (p : Pattern) (ha : d20445 p = 1) (hb : d102052 p = 1) : d19809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d102052 q = 1) : d9389 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44977 q ha hb
    | true =>
      simp only [d16005, d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44971 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d102052 q = 1) : d19805 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d102052 q = 1) : d19806 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d102052 q = 1) : d9330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44971 q ha hb
    | true =>
      simp only [d232, d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44966 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d102052 q = 1) : d19765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d102052 q = 1) : d19766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16008 q = 1) (hb : d102052 q = 1) : d19807 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d102052 q = 1) : d9297 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44966 q ha hb
    | true =>
      simp only [d72, d9297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d102052 q = 1) : d19738 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d19738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d102052 q = 1) : d19739 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d19739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d235 q = 1) (hb : d102052 q = 1) : d19767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d19767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d235, d19767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16009 q = 1) (hb : d102052 q = 1) : d19808 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d19808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16009, d19808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9393 q = 1) (hb : d102052 q = 1) : d9393 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d20445 q = 1) (hb : d102052 q = 1) : d19809 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20445, d19809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20445, d19809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro44979 (p : Pattern) (ha : d20451 p = 1) (hb : d102052 p = 1) : d19815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20446 q = 1) (hb : d102052 q = 1) : d19810 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20446, d19810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44978 q ha hb
    | true =>
      simp only [d20446, d19810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20447 q = 1) (hb : d102052 q = 1) : d19811 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20447, d19811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20447, d19811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20414 q = 1) (hb : d102052 q = 1) : d19770 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d19770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44972 q ha hb
    | true =>
      simp only [d20414, d19770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20415 q = 1) (hb : d102052 q = 1) : d19771 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d19771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, d19771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20448 q = 1) (hb : d102052 q = 1) : d19812 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20448, d19812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20448, d19812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20449 q = 1) (hb : d102052 q = 1) : d19813 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20449, d19813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20449, d19813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20450 q = 1) (hb : d102052 q = 1) : d19814 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20450, d19814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20450, d19814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20451 q = 1) (hb : d102052 q = 1) : d19815 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20451, d19815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20451, d19815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44980 (p : Pattern) (ha : d20465 p = 1) (hb : d102052 p = 1) : d19833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20414 q = 1) (hb : d102052 q = 1) : d19770 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d19770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44972 q ha hb
    | true =>
      simp only [d20414, d19770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20415 q = 1) (hb : d102052 q = 1) : d19771 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d19771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20415, d19771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20462 q = 1) (hb : d102052 q = 1) : d19830 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20462, d19830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20462, d19830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20463 q = 1) (hb : d102052 q = 1) : d19831 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20463, d19831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20463, d19831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20464 q = 1) (hb : d102052 q = 1) : d19832 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20464, d19832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20464, d19832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20465 q = 1) (hb : d102052 q = 1) : d19833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20465, d19833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20465, d19833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44981 (p : Pattern) (ha : d102052 p = 1) (hb : d130940 p = 1) : d130231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20452 q = 1) (hb : d102052 q = 1) : d19816 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20452, d19816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44979 q ha hb
    | true =>
      simp only [d20452, d19816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44973 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d130936 q = 1) : d130227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130936, d130227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130936, d130227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20466 q = 1) (hb : d102052 q = 1) : d19834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20466, d19834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44980 q ha hb
    | true =>
      simp only [d20466, d19834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20467 q = 1) (hb : d102052 q = 1) : d19835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20467, d19835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20467, d19835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130937 q = 1) : d130228 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130937, d130228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130937, d130228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130938 q = 1) : d130229 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130938, d130229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130938, d130229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d130939 q = 1) : d130230 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130939, d130230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130939, d130230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d130940 q = 1) : d130231 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130940, d130231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130940, d130231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44982 (p : Pattern) (ha : d102052 p = 1) (hb : d130946 p = 1) : d130237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d130941 q = 1) : d130232 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130941, d130232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130941, d130232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44981 q ha hb
  have h2 (q : Pattern) (ha : d20478 q = 1) (hb : d102052 q = 1) : d19846 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, d19846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, d19846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44976 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d130942 q = 1) : d130233 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130942, d130233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130942, d130233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d130943 q = 1) : d130234 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130943, d130234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130943, d130234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130944 q = 1) : d130235 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130944, d130235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130944, d130235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130945 q = 1) : d130236 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130945, d130236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130945, d130236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d130946 q = 1) : d130237 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130946, d130237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130946, d130237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44983 (p : Pattern) (ha : d102052 p = 1) (hb : d130952 p = 1) : d130243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20409 q = 1) (hb : d102052 q = 1) : d19761 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20409, d19761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20409, d19761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44970 q ha hb
  have h2 (q : Pattern) (ha : d20410 q = 1) (hb : d102052 q = 1) : d19762 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20410, d19762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20410, d19762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20411 q = 1) (hb : d102052 q = 1) : d19763 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20411, d19763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20411, d19763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20412 q = 1) (hb : d102052 q = 1) : d19764 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20412, d19764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20412, d19764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130931 q = 1) : d130222 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130931, d130222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130931, d130222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44975 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130932 q = 1) : d130223 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130932, d130223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130932, d130223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d130933 q = 1) : d130224 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130933, d130224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130933, d130224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d130934 q = 1) : d130225 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130934, d130225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130934, d130225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d102052 q = 1) (hb : d130935 q = 1) : d130226 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130935, d130226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d130935, d130226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d102052 q = 1) (hb : d130947 q = 1) : d130238 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130947, d130238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130947, d130238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44982 q ha hb
  have h11 (q : Pattern) (ha : d102052 q = 1) (hb : d130948 q = 1) : d130239 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130948, d130239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130948, d130239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d102052 q = 1) (hb : d130949 q = 1) : d130240 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130949, d130240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130949, d130240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102052 q = 1) (hb : d130950 q = 1) : d130241 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130950, d130241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130950, d130241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102052 q = 1) (hb : d130951 q = 1) : d130242 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130951, d130242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130951, d130242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102052 q = 1) (hb : d130952 q = 1) : d130243 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130952, d130243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130952, d130243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro44984 (p : Pattern) (ha : d20500 p = 1) (hb : d102052 p = 1) : d19877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d102052 q = 1) : d9330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44971 q ha hb
    | true =>
      simp only [d232, d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44966 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d102052 q = 1) : d19765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d102052 q = 1) : d19766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d673 q = 1) (hb : d102052 q = 1) : d19867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d19867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d19867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d682 q = 1) (hb : d102052 q = 1) : d19876 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d19876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d682, d19876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9496 q = 1) (hb : d102052 q = 1) : d9496 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20500 q = 1) (hb : d102052 q = 1) : d19877 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20500, d19877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20500, d19877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44985 (p : Pattern) (ha : d20538 p = 1) (hb : d102052 p = 1) : d19921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20501 q = 1) (hb : d102052 q = 1) : d19878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20501, d19878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44984 q ha hb
    | true =>
      simp only [d20501, d19878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20502 q = 1) (hb : d102052 q = 1) : d19879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20502, d19879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20502, d19879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20535 q = 1) (hb : d102052 q = 1) : d19918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20535, d19918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20535, d19918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20536 q = 1) (hb : d102052 q = 1) : d19919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20536, d19919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20536, d19919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20537 q = 1) (hb : d102052 q = 1) : d19920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20537, d19920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20537, d19920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20538 q = 1) (hb : d102052 q = 1) : d19921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20538, d19921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20538, d19921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44986 (p : Pattern) (ha : d20544 p = 1) (hb : d102052 p = 1) : d19927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20539 q = 1) (hb : d102052 q = 1) : d19922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20539, d19922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44985 q ha hb
    | true =>
      simp only [d20539, d19922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20540 q = 1) (hb : d102052 q = 1) : d19923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20540, d19923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20540, d19923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20541 q = 1) (hb : d102052 q = 1) : d19924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20541, d19924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20541, d19924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20542 q = 1) (hb : d102052 q = 1) : d19925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20542, d19925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20542, d19925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20543 q = 1) (hb : d102052 q = 1) : d19926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20543, d19926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20543, d19926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20544 q = 1) (hb : d102052 q = 1) : d19927 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20544, d19927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20544, d19927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44987 (p : Pattern) (ha : d16162 p = 1) (hb : d102052 p = 1) : d9474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d542 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d659 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d543 q = 1) (hb : d102052 q = 1) : d543 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d660 q = 1) (hb : d102052 q = 1) : d9449 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d9449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d660, d9449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d544 q = 1) (hb : d102052 q = 1) : d544 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d661 q = 1) (hb : d102052 q = 1) : d9450 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d9450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d661, d9450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d662 q = 1) (hb : d102052 q = 1) : d9451 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d9451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d662, d9451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9457 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16156 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9458 q = 1) (hb : d102052 q = 1) : d9458 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d16157 q = 1) (hb : d102052 q = 1) : d9459 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d9459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16157, d9459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9460 q = 1) (hb : d102052 q = 1) : d9460 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d16158 q = 1) (hb : d102052 q = 1) : d9461 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d9461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16158, d9461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16159 q = 1) (hb : d102052 q = 1) : d9462 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d9462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16159, d9462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d16160 q = 1) (hb : d102052 q = 1) : d9463 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d9463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16160, d9463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d9467 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12858 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d9468 q = 1) (hb : d102052 q = 1) : d9468 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d12859 q = 1) (hb : d102052 q = 1) : d9469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12859, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9470 q = 1) (hb : d102052 q = 1) : d9470 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d12860 q = 1) (hb : d102052 q = 1) : d9471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d9471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12860, d9471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d12861 q = 1) (hb : d102052 q = 1) : d9472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d9472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12861, d9472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d9381 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d12599 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d9382 q = 1) (hb : d102052 q = 1) : d9382 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d12600 q = 1) (hb : d102052 q = 1) : d9383 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d12600, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d9384 q = 1) (hb : d102052 q = 1) : d9384 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d12601 q = 1) (hb : d102052 q = 1) : d9385 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d9385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d12601, d9385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d12602 q = 1) (hb : d102052 q = 1) : d9386 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d9386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d12602, d9386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h31 (q : Pattern) (ha : d16161 q = 1) (hb : d102052 q = 1) : d9473 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16161, d9473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d16161, d9473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d16162 q = 1) (hb : d102052 q = 1) : d9474 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16162, d9474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16162, d9474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  exact h32 p ha hb
theorem andIntro44988 (p : Pattern) (ha : d16166 p = 1) (hb : d102052 p = 1) : d9478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9381 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12599 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d9382 q = 1) (hb : d102052 q = 1) : d9382 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12600 q = 1) (hb : d102052 q = 1) : d9383 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12600, d9383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9384 q = 1) (hb : d102052 q = 1) : d9384 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12601 q = 1) (hb : d102052 q = 1) : d9385 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d9385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12601, d9385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12602 q = 1) (hb : d102052 q = 1) : d9386 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d9386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12602, d9386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d66 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d25 q = 1) (hb : d102052 q = 1) : d25 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d67 q = 1) (hb : d102052 q = 1) : d9292 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67, d9292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26 q = 1) (hb : d102052 q = 1) : d26 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d68 q = 1) (hb : d102052 q = 1) : d9293 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d9293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68, d9293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d69 q = 1) (hb : d102052 q = 1) : d9294 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d9294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d69, d9294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d12603 q = 1) (hb : d102052 q = 1) : d9387 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d9387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12603, d9387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d70 q = 1) (hb : d102052 q = 1) : d9295 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d9295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d70, d9295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d16166 q = 1) (hb : d102052 q = 1) : d9478 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d9478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16166, d9478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro44989 (p : Pattern) (ha : d20490 p = 1) (hb : d102052 p = 1) : d19864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d102052 q = 1) : d9475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d9475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44987 q ha hb
    | true =>
      simp only [d16163, d9475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44977 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d102052 q = 1) : d19858 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d19858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d19858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d102052 q = 1) : d19859 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d19859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d19859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d102052 q = 1) : d9479 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d9479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44977 q ha hb
    | true =>
      simp only [d16167, d9479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44988 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d102052 q = 1) : d19860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d19860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d19860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d102052 q = 1) : d19861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d19861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d19861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d102052 q = 1) : d19862 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d19862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d19862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d102052 q = 1) : d9389 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44977 q ha hb
    | true =>
      simp only [d16005, d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44971 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d102052 q = 1) : d19805 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d102052 q = 1) : d19806 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d232 q = 1) (hb : d102052 q = 1) : d9330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44971 q ha hb
    | true =>
      simp only [d232, d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44966 q ha hb
  have h12 (q : Pattern) (ha : d233 q = 1) (hb : d102052 q = 1) : d19765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d234 q = 1) (hb : d102052 q = 1) : d19766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16008 q = 1) (hb : d102052 q = 1) : d19807 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16171 q = 1) (hb : d102052 q = 1) : d19863 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d19863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d19863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9483 q = 1) (hb : d102052 q = 1) : d9483 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d20490 q = 1) (hb : d102052 q = 1) : d19864 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20490, d19864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20490, d19864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro44990 (p : Pattern) (ha : d20493 p = 1) (hb : d102052 p = 1) : d19869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d102052 q = 1) : d9389 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44977 q ha hb
    | true =>
      simp only [d16005, d9389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44971 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d102052 q = 1) : d19805 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d19805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d102052 q = 1) : d19806 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d19806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d232 q = 1) (hb : d102052 q = 1) : d9330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44971 q ha hb
    | true =>
      simp only [d232, d9330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44966 q ha hb
  have h5 (q : Pattern) (ha : d233 q = 1) (hb : d102052 q = 1) : d19765 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d19765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d234 q = 1) (hb : d102052 q = 1) : d19766 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d19766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16008 q = 1) (hb : d102052 q = 1) : d19807 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d19807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d673 q = 1) (hb : d102052 q = 1) : d19867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d19867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d673, d19867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16175 q = 1) (hb : d102052 q = 1) : d19868 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d19868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16175, d19868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9488 q = 1) (hb : d102052 q = 1) : d9488 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d20493 q = 1) (hb : d102052 q = 1) : d19869 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20493, d19869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20493, d19869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro44991 (p : Pattern) (ha : d20499 p = 1) (hb : d102052 p = 1) : d19875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20491 q = 1) (hb : d102052 q = 1) : d19865 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20491, d19865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44989 q ha hb
    | true =>
      simp only [d20491, d19865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20492 q = 1) (hb : d102052 q = 1) : d19866 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20492, d19866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20492, d19866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20494 q = 1) (hb : d102052 q = 1) : d19870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d19870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44990 q ha hb
    | true =>
      simp only [d20494, d19870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20495 q = 1) (hb : d102052 q = 1) : d19871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d19871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, d19871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20496 q = 1) (hb : d102052 q = 1) : d19872 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20496, d19872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20496, d19872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20497 q = 1) (hb : d102052 q = 1) : d19873 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20497, d19873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20497, d19873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20498 q = 1) (hb : d102052 q = 1) : d19874 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20498, d19874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20498, d19874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20499 q = 1) (hb : d102052 q = 1) : d19875 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20499, d19875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20499, d19875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44992 (p : Pattern) (ha : d20506 p = 1) (hb : d102052 p = 1) : d19883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20494 q = 1) (hb : d102052 q = 1) : d19870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d19870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44990 q ha hb
    | true =>
      simp only [d20494, d19870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20495 q = 1) (hb : d102052 q = 1) : d19871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d19871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, d19871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20501 q = 1) (hb : d102052 q = 1) : d19878 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20501, d19878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44984 q ha hb
    | true =>
      simp only [d20501, d19878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20502 q = 1) (hb : d102052 q = 1) : d19879 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20502, d19879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20502, d19879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20503 q = 1) (hb : d102052 q = 1) : d19880 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20503, d19880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20503, d19880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20504 q = 1) (hb : d102052 q = 1) : d19881 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20504, d19881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20504, d19881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20505 q = 1) (hb : d102052 q = 1) : d19882 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20505, d19882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20505, d19882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20506 q = 1) (hb : d102052 q = 1) : d19883 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20506, d19883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20506, d19883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro44993 (p : Pattern) (ha : d20527 p = 1) (hb : d102052 p = 1) : d19910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20494 q = 1) (hb : d102052 q = 1) : d19870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d19870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44990 q ha hb
    | true =>
      simp only [d20494, d19870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20495 q = 1) (hb : d102052 q = 1) : d19871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d19871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20495, d19871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20524 q = 1) (hb : d102052 q = 1) : d19907 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20524, d19907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20524, d19907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20525 q = 1) (hb : d102052 q = 1) : d19908 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20525, d19908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20525, d19908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20526 q = 1) (hb : d102052 q = 1) : d19909 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20526, d19909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20526, d19909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20527 q = 1) (hb : d102052 q = 1) : d19910 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20527, d19910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20527, d19910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro44994 (p : Pattern) (ha : d102052 p = 1) (hb : d130957 p = 1) : d130248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20507 q = 1) (hb : d102052 q = 1) : d19884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20507, d19884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44991 q ha hb
    | true =>
      simp only [d20507, d19884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44992 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d130953 q = 1) : d130244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130953, d130244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130953, d130244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20528 q = 1) (hb : d102052 q = 1) : d19911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20528, d19911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44993 q ha hb
    | true =>
      simp only [d20528, d19911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20529 q = 1) (hb : d102052 q = 1) : d19912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20529, d19912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20529, d19912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130954 q = 1) : d130245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130954, d130245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130954, d130245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130955 q = 1) : d130246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130955, d130246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130955, d130246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d130956 q = 1) : d130247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130956, d130247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130956, d130247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d130957 q = 1) : d130248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130957, d130248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130957, d130248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro44995 (p : Pattern) (ha : d102052 p = 1) (hb : d130963 p = 1) : d130254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d130958 q = 1) : d130249 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130958, d130249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130958, d130249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44994 q ha hb
  have h2 (q : Pattern) (ha : d20545 q = 1) (hb : d102052 q = 1) : d19928 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20545, d19928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20545, d19928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44986 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d130959 q = 1) : d130250 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130959, d130250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130959, d130250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d130960 q = 1) : d130251 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130960, d130251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130960, d130251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130961 q = 1) : d130252 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130961, d130252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130961, d130252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130962 q = 1) : d130253 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130962, d130253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130962, d130253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d130963 q = 1) : d130254 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130963, d130254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130963, d130254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro44996 (p : Pattern) (ha : d102052 p = 1) (hb : d130969 p = 1) : d130260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d130964 q = 1) : d130255 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130964, d130255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130964, d130255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44995 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d130965 q = 1) : d130256 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130965, d130256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130965, d130256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d130966 q = 1) : d130257 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130966, d130257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130966, d130257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d130967 q = 1) : d130258 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130967, d130258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130967, d130258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130968 q = 1) : d130259 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130968, d130259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130968, d130259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130969 q = 1) : d130260 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130969, d130260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130969, d130260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro44997 (p : Pattern) (ha : d981 p = 1) (hb : d102052 p = 1) : d9619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d412 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d319 q = 1) (hb : d102052 q = 1) : d319 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d413 q = 1) (hb : d102052 q = 1) : d9377 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d413, d9377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320 q = 1) (hb : d102052 q = 1) : d320 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d414 q = 1) (hb : d102052 q = 1) : d9378 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d9378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d414, d9378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d415 q = 1) (hb : d102052 q = 1) : d9379 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d9379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d415, d9379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d750 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d971 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d751 q = 1) (hb : d102052 q = 1) : d751 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d972 q = 1) (hb : d102052 q = 1) : d9604 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d972, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d752 q = 1) (hb : d102052 q = 1) : d752 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d973 q = 1) (hb : d102052 q = 1) : d9605 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d9605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d973, d9605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d974 q = 1) (hb : d102052 q = 1) : d9606 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d9606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d974, d9606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d975 q = 1) (hb : d102052 q = 1) : d9618 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d9618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d975, d9618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d980 q = 1) (hb : d102052 q = 1) : d9612 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d9612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d980, d9612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d981 q = 1) (hb : d102052 q = 1) : d9619 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d9619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d981, d9619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro44998 (p : Pattern) (ha : d986 p = 1) (hb : d102052 p = 1) : d9623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d971 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d751 q = 1) (hb : d102052 q = 1) : d751 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d972 q = 1) (hb : d102052 q = 1) : d9604 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d972, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d752 q = 1) (hb : d102052 q = 1) : d752 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d973 q = 1) (hb : d102052 q = 1) : d9605 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d9605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d973, d9605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d974 q = 1) (hb : d102052 q = 1) : d9606 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d9606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d974, d9606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d980 q = 1) (hb : d102052 q = 1) : d9612 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d9612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d980, d9612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d986 q = 1) (hb : d102052 q = 1) : d9623 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d9623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d986, d9623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro44999 (p : Pattern) (ha : d20568 p = 1) (hb : d102052 p = 1) : d19965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d102052 q = 1) : d9624 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44997 q ha hb
    | true =>
      simp only [d987, d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44998 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d102052 q = 1) : d19948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d102052 q = 1) : d19949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d102052 q = 1) : d19955 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d19955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d19955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d102052 q = 1) : d19964 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d19964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d19964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9641 q = 1) (hb : d102052 q = 1) : d9641 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20568 q = 1) (hb : d102052 q = 1) : d19965 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20568, d19965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20568, d19965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
end NetHack.Soko22Hazard87
