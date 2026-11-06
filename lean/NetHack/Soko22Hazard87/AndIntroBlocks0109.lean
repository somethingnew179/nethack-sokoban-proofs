import NetHack.Soko22Hazard87.AndIntroBlocks0108
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro27250 (p : Pattern) (ha : d74590 p = 1) (hb : d109112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d386 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10668 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4376 q = 1) (hb : d10722 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d10722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4376, d10722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10723 q = 1) (hb : d74580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d10723, d74580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10724 q = 1) (hb : d74588 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d74588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d74588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10725 q = 1) (hb : d74589 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d74589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d74589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74590 q = 1) (hb : d109112 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74590, d109112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74590, d109112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27251 (p : Pattern) (ha : d74599 p = 1) (hb : d109122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d430 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10698 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4391 q = 1) (hb : d109118 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d109118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4391, d109118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74596 q = 1) (hb : d109119 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74596, d109119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74596, d109119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74597 q = 1) (hb : d109120 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74597, d109120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74597, d109120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74598 q = 1) (hb : d109121 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74598, d109121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74598, d109121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74599 q = 1) (hb : d109122 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74599, d109122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74599, d109122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27252 (p : Pattern) (ha : d74605 p = 1) (hb : d109128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10727 q = 1) (hb : d74584 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d74584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27248 q ha hb
    | true =>
      simp only [d10727, d74584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27249 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10728 q = 1) (hb : d74585 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d74585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10728, d74585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74586 q = 1) (hb : d109110 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74586, d109110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74586, d109110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74587 q = 1) (hb : d109111 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74587, d109111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74587, d109111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74591 q = 1) (hb : d109113 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74591, d109113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74591, d109113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27250 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74592 q = 1) (hb : d109114 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74592, d109114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74592, d109114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74593 q = 1) (hb : d109115 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74593, d109115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74593, d109115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74594 q = 1) (hb : d109116 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74594, d109116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74594, d109116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74595 q = 1) (hb : d109117 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74595, d109117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74595, d109117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74600 q = 1) (hb : d109123 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74600, d109123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74600, d109123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27251 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74601 q = 1) (hb : d109124 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74601, d109124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74601, d109124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74602 q = 1) (hb : d109125 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74602, d109125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74602, d109125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74603 q = 1) (hb : d109126 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74603, d109126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74603, d109126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74604 q = 1) (hb : d109127 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74604, d109127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74604, d109127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74605 q = 1) (hb : d109128 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74605, d109128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74605, d109128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27253 (p : Pattern) (ha : d74611 p = 1) (hb : d109134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro376 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74606 q = 1) (hb : d109129 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74606, d109129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74606, d109129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27252 q ha hb
  have h8 (q : Pattern) (ha : d74607 q = 1) (hb : d109130 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74607, d109130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74607, d109130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74608 q = 1) (hb : d109131 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74608, d109131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74608, d109131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74609 q = 1) (hb : d109132 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74609, d109132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74609, d109132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74610 q = 1) (hb : d109133 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74610, d109133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74610, d109133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74611 q = 1) (hb : d109134 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74611, d109134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74611, d109134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27254 (p : Pattern) (ha : d10885 p = 1) (hb : d74615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d10880 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4408 q = 1) (hb : d10881 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d10881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4408, d10881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10882 q = 1) (hb : d74612 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d74612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d10882, d74612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10883 q = 1) (hb : d74613 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d74613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10883, d74613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10884 q = 1) (hb : d74614 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d74614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10884, d74614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10885 q = 1) (hb : d74615 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d74615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10885, d74615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27255 (p : Pattern) (ha : d10895 p = 1) (hb : d74619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10880 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4408 q = 1) (hb : d10881 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d10881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4408, d10881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5401 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10882 q = 1) (hb : d74612 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d74612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d10882, d74612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10883 q = 1) (hb : d74613 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d74613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10883, d74613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10884 q = 1) (hb : d74614 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d74614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d74614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d614 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d619 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d621 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d10890 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4413 q = 1) (hb : d10891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d10891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4413, d10891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d10892 q = 1) (hb : d74616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d74616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d10892, d74616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10893 q = 1) (hb : d74617 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d74617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10893, d74617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10894 q = 1) (hb : d74618 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d74618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10894, d74618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10895 q = 1) (hb : d74619 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d74619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10895, d74619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27256 (p : Pattern) (ha : d74626 p = 1) (hb : d109137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10890 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4413 q = 1) (hb : d10891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d10891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4413, d10891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5408 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10892 q = 1) (hb : d74616 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d74616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d10892, d74616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10893 q = 1) (hb : d74624 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d74624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d74624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10894 q = 1) (hb : d74625 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d74625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d74625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74626 q = 1) (hb : d109137 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74626, d109137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74626, d109137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27257 (p : Pattern) (ha : d74635 p = 1) (hb : d109148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109143 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4428 q = 1) (hb : d109144 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d109144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4428, d109144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5430 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74632 q = 1) (hb : d109145 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74632, d109145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74632, d109145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74633 q = 1) (hb : d109146 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74633, d109146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74633, d109146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74634 q = 1) (hb : d109147 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74634, d109147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74634, d109147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74635 q = 1) (hb : d109148 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74635, d109148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74635, d109148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27258 (p : Pattern) (ha : d74641 p = 1) (hb : d109154 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10896 q = 1) (hb : d74620 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d74620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27254 q ha hb
    | true =>
      simp only [d10896, d74620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27255 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d645 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10897 q = 1) (hb : d74621 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d74621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10897, d74621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74622 q = 1) (hb : d109135 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74622, d109135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74622, d109135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74623 q = 1) (hb : d109136 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74623, d109136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74623, d109136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74627 q = 1) (hb : d109138 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74627, d109138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74627, d109138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27256 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74628 q = 1) (hb : d109139 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74628, d109139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74628, d109139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74629 q = 1) (hb : d109140 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74629, d109140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74629, d109140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74630 q = 1) (hb : d109141 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74630, d109141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74630, d109141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74631 q = 1) (hb : d109142 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74631, d109142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74631, d109142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74636 q = 1) (hb : d109149 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74636, d109149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74636, d109149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27257 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74637 q = 1) (hb : d109150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74637, d109150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74637, d109150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74638 q = 1) (hb : d109151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74638, d109151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74638, d109151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74639 q = 1) (hb : d109152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74639, d109152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74639, d109152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74640 q = 1) (hb : d109153 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74640, d109153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74640, d109153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74641 q = 1) (hb : d109154 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74641, d109154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74641, d109154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27259 (p : Pattern) (ha : d74647 p = 1) (hb : d109160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74642 q = 1) (hb : d109155 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74642, d109155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74642, d109155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27258 q ha hb
  have h2 (q : Pattern) (ha : d74643 q = 1) (hb : d109156 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74643, d109156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74643, d109156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74644 q = 1) (hb : d109157 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74644, d109157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74644, d109157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74645 q = 1) (hb : d109158 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74645, d109158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74645, d109158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74646 q = 1) (hb : d109159 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74646, d109159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74646, d109159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74647 q = 1) (hb : d109160 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74647, d109160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74647, d109160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27260 (p : Pattern) (ha : d11125 p = 1) (hb : d74652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11120 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4446 q = 1) (hb : d11121 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d11121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4446, d11121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5471 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11122 q = 1) (hb : d74649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d74649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d11122, d74649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11123 q = 1) (hb : d74650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d74650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11123, d74650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11124 q = 1) (hb : d74651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d74651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11124, d74651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11125 q = 1) (hb : d74652 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d74652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11125, d74652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27261 (p : Pattern) (ha : d11135 p = 1) (hb : d74656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11120 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4446 q = 1) (hb : d11121 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d11121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4446, d11121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5471 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11122 q = 1) (hb : d74649 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d74649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d11122, d74649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11123 q = 1) (hb : d74650 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d74650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11123, d74650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11124 q = 1) (hb : d74651 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d74651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d74651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d920 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d925 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d927 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d11130 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4451 q = 1) (hb : d11131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d11131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4451, d11131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5478 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d11132 q = 1) (hb : d74653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d74653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d11132, d74653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11133 q = 1) (hb : d74654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d74654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11133, d74654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11134 q = 1) (hb : d74655 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d74655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11134, d74655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11135 q = 1) (hb : d74656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d74656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11135, d74656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27262 (p : Pattern) (ha : d74663 p = 1) (hb : d109164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d927 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4451 q = 1) (hb : d11131 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d11131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4451, d11131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5478 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11132 q = 1) (hb : d74653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d74653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d11132, d74653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11133 q = 1) (hb : d74661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d74661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d74661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11134 q = 1) (hb : d74662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d74662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d74662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74663 q = 1) (hb : d109164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74663, d109164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74663, d109164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27263 (p : Pattern) (ha : d74672 p = 1) (hb : d109175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1012 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109170 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4466 q = 1) (hb : d109171 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d109171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4466, d109171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5515 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74669 q = 1) (hb : d109172 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74669, d109172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74669, d109172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74670 q = 1) (hb : d109173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74670, d109173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74670, d109173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74671 q = 1) (hb : d109174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74671, d109174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74671, d109174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74672 q = 1) (hb : d109175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74672, d109175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74672, d109175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27264 (p : Pattern) (ha : d74678 p = 1) (hb : d109181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11136 q = 1) (hb : d74657 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d74657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27260 q ha hb
    | true =>
      simp only [d11136, d74657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27261 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11137 q = 1) (hb : d74658 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d74658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11137, d74658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74659 q = 1) (hb : d109162 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74659, d109162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74659, d109162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74660 q = 1) (hb : d109163 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74660, d109163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74660, d109163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74664 q = 1) (hb : d109165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74664, d109165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74664, d109165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27262 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74665 q = 1) (hb : d109166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74665, d109166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74665, d109166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74666 q = 1) (hb : d109167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74666, d109167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74666, d109167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74667 q = 1) (hb : d109168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74667, d109168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74667, d109168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74668 q = 1) (hb : d109169 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74668, d109169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74668, d109169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74673 q = 1) (hb : d109176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74673, d109176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74673, d109176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27263 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74674 q = 1) (hb : d109177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74674, d109177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74674, d109177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74675 q = 1) (hb : d109178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74675, d109178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74675, d109178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74676 q = 1) (hb : d109179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74676, d109179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74676, d109179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74677 q = 1) (hb : d109180 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74677, d109180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74677, d109180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74678 q = 1) (hb : d109181 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74678, d109181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74678, d109181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27265 (p : Pattern) (ha : d74684 p = 1) (hb : d109187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74679 q = 1) (hb : d109182 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74679, d109182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74679, d109182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27264 q ha hb
  have h2 (q : Pattern) (ha : d74680 q = 1) (hb : d109183 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74680, d109183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74680, d109183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74681 q = 1) (hb : d109184 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74681, d109184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74681, d109184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74682 q = 1) (hb : d109185 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74682, d109185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74682, d109185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74683 q = 1) (hb : d109186 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74683, d109186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74683, d109186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74684 q = 1) (hb : d109187 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74684, d109187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74684, d109187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27266 (p : Pattern) (ha : d11395 p = 1) (hb : d74690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11390 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4485 q = 1) (hb : d11391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d11391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4485, d11391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5560 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11392 q = 1) (hb : d74687 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d74687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d11392, d74687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11393 q = 1) (hb : d74688 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d74688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11393, d74688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11394 q = 1) (hb : d74689 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d74689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11394, d74689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11395 q = 1) (hb : d74690 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11395, d74690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11395, d74690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27267 (p : Pattern) (ha : d11405 p = 1) (hb : d74694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11390 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4485 q = 1) (hb : d11391 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d11391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4485, d11391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5560 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11392 q = 1) (hb : d74687 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d74687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d11392, d74687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11393 q = 1) (hb : d74688 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d74688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11393, d74688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11394 q = 1) (hb : d74689 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d74689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d74689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1331 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1336 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d11400 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4490 q = 1) (hb : d11401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d11401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4490, d11401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5567 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d11402 q = 1) (hb : d74691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d74691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d11402, d74691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11403 q = 1) (hb : d74692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d74692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11403, d74692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11404 q = 1) (hb : d74693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d74693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11404, d74693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11405 q = 1) (hb : d74694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11405, d74694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11405, d74694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27268 (p : Pattern) (ha : d74701 p = 1) (hb : d109192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4490 q = 1) (hb : d11401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d11401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4490, d11401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5567 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11402 q = 1) (hb : d74691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d74691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d11402, d74691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11403 q = 1) (hb : d74699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d74699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d74699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11404 q = 1) (hb : d74700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d74700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d74700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74701 q = 1) (hb : d109192 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74701, d109192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74701, d109192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27269 (p : Pattern) (ha : d74710 p = 1) (hb : d109203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4505 q = 1) (hb : d109199 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d109199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4505, d109199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5604 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74707 q = 1) (hb : d109200 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74707, d109200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74707, d109200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74708 q = 1) (hb : d109201 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74708, d109201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74708, d109201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74709 q = 1) (hb : d109202 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74709, d109202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74709, d109202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74710 q = 1) (hb : d109203 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74710, d109203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74710, d109203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27270 (p : Pattern) (ha : d74716 p = 1) (hb : d109209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11406 q = 1) (hb : d74695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d74695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27266 q ha hb
    | true =>
      simp only [d11406, d74695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27267 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11407 q = 1) (hb : d74696 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d74696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11407, d74696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74697 q = 1) (hb : d109190 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74697, d109190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74697, d109190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74698 q = 1) (hb : d109191 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74698, d109191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74698, d109191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74702 q = 1) (hb : d109193 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74702, d109193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74702, d109193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27268 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74703 q = 1) (hb : d109194 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74703, d109194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74703, d109194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74704 q = 1) (hb : d109195 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74704, d109195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74704, d109195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74705 q = 1) (hb : d109196 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74705, d109196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74705, d109196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74706 q = 1) (hb : d109197 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74706, d109197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74706, d109197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74711 q = 1) (hb : d109204 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74711, d109204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74711, d109204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27269 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74712 q = 1) (hb : d109205 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74712, d109205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74712, d109205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74713 q = 1) (hb : d109206 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74713, d109206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74713, d109206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74714 q = 1) (hb : d109207 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74714, d109207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74714, d109207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74715 q = 1) (hb : d109208 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74715, d109208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74715, d109208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74716 q = 1) (hb : d109209 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74716, d109209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74716, d109209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27271 (p : Pattern) (ha : d74722 p = 1) (hb : d109215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74717 q = 1) (hb : d109210 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74717, d109210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74717, d109210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27270 q ha hb
  have h2 (q : Pattern) (ha : d74718 q = 1) (hb : d109211 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74718, d109211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74718, d109211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74719 q = 1) (hb : d109212 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74719, d109212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74719, d109212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74720 q = 1) (hb : d109213 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74720, d109213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74720, d109213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74721 q = 1) (hb : d109214 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74721, d109214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74721, d109214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74722 q = 1) (hb : d109215 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74722, d109215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74722, d109215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27272 (p : Pattern) (ha : d11666 p = 1) (hb : d74729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11661 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4525 q = 1) (hb : d11662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d11662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4525, d11662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5650 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11663 q = 1) (hb : d74726 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d74726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d11663, d74726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11664 q = 1) (hb : d74727 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d74727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11664, d74727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11665 q = 1) (hb : d74728 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d74728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11665, d74728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11666 q = 1) (hb : d74729 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d74729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11666, d74729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27273 (p : Pattern) (ha : d11676 p = 1) (hb : d74733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11661 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4525 q = 1) (hb : d11662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d11662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4525, d11662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5650 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11663 q = 1) (hb : d74726 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d74726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d11663, d74726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11664 q = 1) (hb : d74727 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d74727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11664, d74727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11665 q = 1) (hb : d74728 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d74728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d74728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d11671 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4530 q = 1) (hb : d11672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d11672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4530, d11672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5657 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d11673 q = 1) (hb : d74730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d74730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d11673, d74730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11674 q = 1) (hb : d74731 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d74731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11674, d74731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11675 q = 1) (hb : d74732 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d74732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11675, d74732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11676 q = 1) (hb : d74733 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d74733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11676, d74733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27274 (p : Pattern) (ha : d74740 p = 1) (hb : d109221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11671 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4530 q = 1) (hb : d11672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d11672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4530, d11672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5657 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11673 q = 1) (hb : d74730 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d74730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d11673, d74730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11674 q = 1) (hb : d74738 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d74738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d74738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11675 q = 1) (hb : d74739 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d74739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d74739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74740 q = 1) (hb : d109221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74740, d109221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74740, d109221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27275 (p : Pattern) (ha : d74749 p = 1) (hb : d109232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1914 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4545 q = 1) (hb : d109228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d109228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4545, d109228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5694 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74746 q = 1) (hb : d109229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74746, d109229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74746, d109229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74747 q = 1) (hb : d109230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74747, d109230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74747, d109230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74748 q = 1) (hb : d109231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74748, d109231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74748, d109231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74749 q = 1) (hb : d109232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74749, d109232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74749, d109232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27276 (p : Pattern) (ha : d74755 p = 1) (hb : d109238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11677 q = 1) (hb : d74734 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d74734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27272 q ha hb
    | true =>
      simp only [d11677, d74734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27273 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11678 q = 1) (hb : d74735 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d74735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11678, d74735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74736 q = 1) (hb : d109219 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74736, d109219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74736, d109219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74737 q = 1) (hb : d109220 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74737, d109220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74737, d109220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74741 q = 1) (hb : d109222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74741, d109222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74741, d109222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27274 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74742 q = 1) (hb : d109223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74742, d109223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74742, d109223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74743 q = 1) (hb : d109224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74743, d109224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74743, d109224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74744 q = 1) (hb : d109225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74744, d109225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74744, d109225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74745 q = 1) (hb : d109226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74745, d109226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74745, d109226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74750 q = 1) (hb : d109233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74750, d109233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74750, d109233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27275 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74751 q = 1) (hb : d109234 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74751, d109234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74751, d109234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74752 q = 1) (hb : d109235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74752, d109235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74752, d109235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74753 q = 1) (hb : d109236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74753, d109236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74753, d109236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74754 q = 1) (hb : d109237 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74754, d109237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74754, d109237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74755 q = 1) (hb : d109238 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74755, d109238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74755, d109238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27277 (p : Pattern) (ha : d74761 p = 1) (hb : d109244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74756 q = 1) (hb : d109239 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74756, d109239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74756, d109239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27276 q ha hb
  have h2 (q : Pattern) (ha : d74757 q = 1) (hb : d109240 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74757, d109240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74757, d109240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74758 q = 1) (hb : d109241 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74758, d109241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74758, d109241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74759 q = 1) (hb : d109242 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74759, d109242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74759, d109242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74760 q = 1) (hb : d109243 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74760, d109243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74760, d109243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74761 q = 1) (hb : d109244 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74761, d109244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74761, d109244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27278 (p : Pattern) (ha : d11938 p = 1) (hb : d74769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11933 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4566 q = 1) (hb : d11934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d11934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4566, d11934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5741 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11935 q = 1) (hb : d74766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d74766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d11935, d74766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11936 q = 1) (hb : d74767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d74767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11936, d74767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11937 q = 1) (hb : d74768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d74768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11937, d74768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11938 q = 1) (hb : d74769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11938, d74769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11938, d74769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27279 (p : Pattern) (ha : d11948 p = 1) (hb : d74773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11933 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4566 q = 1) (hb : d11934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d11934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4566, d11934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5741 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11935 q = 1) (hb : d74766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d74766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d11935, d74766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11936 q = 1) (hb : d74767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d74767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11936, d74767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11937 q = 1) (hb : d74768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d74768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d74768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2286 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2291 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d11943 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4571 q = 1) (hb : d11944 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d11944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4571, d11944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5748 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d11945 q = 1) (hb : d74770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d74770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d11945, d74770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11946 q = 1) (hb : d74771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d74771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11946, d74771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11947 q = 1) (hb : d74772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d74772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11947, d74772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11948 q = 1) (hb : d74773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11948, d74773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11948, d74773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro27280 (p : Pattern) (ha : d74780 p = 1) (hb : d109251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11943 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4571 q = 1) (hb : d11944 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d11944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4571, d11944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5748 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11945 q = 1) (hb : d74770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d74770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d11945, d74770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11946 q = 1) (hb : d74778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d74778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d74778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11947 q = 1) (hb : d74779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d74779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d74779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74780 q = 1) (hb : d109251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74780, d109251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74780, d109251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro27281 (p : Pattern) (ha : d74789 p = 1) (hb : d109262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109257 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4586 q = 1) (hb : d109258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d109258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4586, d109258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5785 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74786 q = 1) (hb : d109259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74786, d109259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74786, d109259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74787 q = 1) (hb : d109260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74787, d109260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74787, d109260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74788 q = 1) (hb : d109261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74788, d109261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74788, d109261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74789 q = 1) (hb : d109262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74789, d109262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74789, d109262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27282 (p : Pattern) (ha : d74795 p = 1) (hb : d109268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11949 q = 1) (hb : d74774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d74774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27278 q ha hb
    | true =>
      simp only [d11949, d74774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27279 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11950 q = 1) (hb : d74775 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d74775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11950, d74775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74776 q = 1) (hb : d109249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74776, d109249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d74776, d109249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74777 q = 1) (hb : d109250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74777, d109250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74777, d109250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74781 q = 1) (hb : d109252 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74781, d109252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74781, d109252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27280 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74782 q = 1) (hb : d109253 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74782, d109253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74782, d109253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74783 q = 1) (hb : d109254 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74783, d109254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74783, d109254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74784 q = 1) (hb : d109255 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74784, d109255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74784, d109255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74785 q = 1) (hb : d109256 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74785, d109256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74785, d109256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74790 q = 1) (hb : d109263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74790, d109263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74790, d109263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27281 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74791 q = 1) (hb : d109264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74791, d109264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74791, d109264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74792 q = 1) (hb : d109265 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74792, d109265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74792, d109265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74793 q = 1) (hb : d109266 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74793, d109266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74793, d109266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74794 q = 1) (hb : d109267 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74794, d109267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74794, d109267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74795 q = 1) (hb : d109268 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74795, d109268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74795, d109268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27283 (p : Pattern) (ha : d74801 p = 1) (hb : d109274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74796 q = 1) (hb : d109269 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74796, d109269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74796, d109269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27282 q ha hb
  have h2 (q : Pattern) (ha : d74797 q = 1) (hb : d109270 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74797, d109270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74797, d109270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74798 q = 1) (hb : d109271 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74798, d109271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74798, d109271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74799 q = 1) (hb : d109272 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74799, d109272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74799, d109272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74800 q = 1) (hb : d109273 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74800, d109273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74800, d109273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74801 q = 1) (hb : d109274 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74801, d109274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74801, d109274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27284 (p : Pattern) (ha : d74807 p = 1) (hb : d109280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74648 q = 1) (hb : d109161 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74648, d109161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27253 q ha hb
    | true =>
      simp only [d74648, d109161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74685 q = 1) (hb : d109188 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74685, d109188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74685, d109188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27265 q ha hb
  have h3 (q : Pattern) (ha : d74686 q = 1) (hb : d109189 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74686, d109189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74686, d109189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74723 q = 1) (hb : d109216 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74723, d109216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74723, d109216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27271 q ha hb
  have h5 (q : Pattern) (ha : d74724 q = 1) (hb : d109217 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74724, d109217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74724, d109217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74725 q = 1) (hb : d109218 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74725, d109218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74725, d109218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74762 q = 1) (hb : d109245 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74762, d109245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74762, d109245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27277 q ha hb
  have h8 (q : Pattern) (ha : d74763 q = 1) (hb : d109246 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74763, d109246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74763, d109246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74764 q = 1) (hb : d109247 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74764, d109247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74764, d109247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74765 q = 1) (hb : d109248 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74765, d109248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74765, d109248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74802 q = 1) (hb : d109275 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74802, d109275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74802, d109275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27283 q ha hb
  have h12 (q : Pattern) (ha : d74803 q = 1) (hb : d109276 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74803, d109276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74803, d109276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74804 q = 1) (hb : d109277 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74804, d109277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74804, d109277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74805 q = 1) (hb : d109278 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74805, d109278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74805, d109278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74806 q = 1) (hb : d109279 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74806, d109279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74806, d109279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74807 q = 1) (hb : d109280 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74807, d109280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74807, d109280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro27285 (p : Pattern) (ha : d74813 p = 1) (hb : d109286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74808 q = 1) (hb : d109281 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74808, d109281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27284 q ha hb
    | true =>
      simp only [d74808, d109281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74809 q = 1) (hb : d109282 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74809, d109282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74809, d109282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74810 q = 1) (hb : d109283 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74810, d109283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74810, d109283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74811 q = 1) (hb : d109284 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74811, d109284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74811, d109284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74812 q = 1) (hb : d109285 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74812, d109285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74812, d109285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74813 q = 1) (hb : d109286 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74813, d109286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74813, d109286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27286 (p : Pattern) (ha : d74819 p = 1) (hb : d109292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74814 q = 1) (hb : d109287 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74814, d109287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27285 q ha hb
    | true =>
      simp only [d74814, d109287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74815 q = 1) (hb : d109288 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74815, d109288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74815, d109288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74816 q = 1) (hb : d109289 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74816, d109289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74816, d109289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74817 q = 1) (hb : d109290 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74817, d109290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74817, d109290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74818 q = 1) (hb : d109291 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74818, d109291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74818, d109291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74819 q = 1) (hb : d109292 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74819, d109292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74819, d109292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27287 (p : Pattern) (ha : d74825 p = 1) (hb : d109298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74820 q = 1) (hb : d109293 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74820, d109293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27286 q ha hb
    | true =>
      simp only [d74820, d109293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74821 q = 1) (hb : d109294 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74821, d109294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74821, d109294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74822 q = 1) (hb : d109295 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74822, d109295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74822, d109295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74823 q = 1) (hb : d109296 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74823, d109296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74823, d109296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74824 q = 1) (hb : d109297 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74824, d109297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74824, d109297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74825 q = 1) (hb : d109298 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74825, d109298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74825, d109298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27288 (p : Pattern) (ha : d74831 p = 1) (hb : d109304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74826 q = 1) (hb : d109299 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, d109299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27287 q ha hb
    | true =>
      simp only [d74826, d109299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74827 q = 1) (hb : d109300 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, d109300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74827, d109300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74828 q = 1) (hb : d109301 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, d109301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74828, d109301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74829 q = 1) (hb : d109302 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d109302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74829, d109302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74830 q = 1) (hb : d109303 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, d109303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74830, d109303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74831 q = 1) (hb : d109304 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d109304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74831, d109304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27289 (p : Pattern) (ha : d74837 p = 1) (hb : d109310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d109305 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, d109305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27288 q ha hb
    | true =>
      simp only [d74832, d109305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d109306 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, d109306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, d109306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d109307 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, d109307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, d109307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d109308 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, d109308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, d109308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d109309 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, d109309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, d109309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d109310 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, d109310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, d109310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27290 (p : Pattern) (ha : d74843 p = 1) (hb : d109316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d109311 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, d109311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27289 q ha hb
    | true =>
      simp only [d74838, d109311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d109312 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, d109312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, d109312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d109313 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, d109313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, d109313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d109314 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, d109314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, d109314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d109315 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, d109315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, d109315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d109316 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, d109316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, d109316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27291 (p : Pattern) (ha : d74849 p = 1) (hb : d109322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d109317 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, d109317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27290 q ha hb
    | true =>
      simp only [d74844, d109317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d109318 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, d109318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, d109318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d109319 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, d109319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, d109319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d109320 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, d109320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, d109320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d109321 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, d109321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, d109321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d109322 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, d109322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, d109322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27292 (p : Pattern) (ha : d109091 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d109087 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d109088 q = 1) (hb : d132771 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d132771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109088, d132771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d109089 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d132772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109089, d132772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d109090 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109091 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro27293 (p : Pattern) (ha : d109097 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109092 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27292 q ha hb
    | true =>
      simp only [d109092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109093 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109094 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109095 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109096 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109097 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27294 (p : Pattern) (ha : d109103 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109098 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27293 q ha hb
    | true =>
      simp only [d109098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109099 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109100 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109101 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109102 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109103 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27295 (p : Pattern) (ha : d109109 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109104 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27294 q ha hb
    | true =>
      simp only [d109104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109105 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109106 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109107 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109108 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109109 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27296 (p : Pattern) (ha : d109304 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d109300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d109301 q = 1) (hb : d132771 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109301, d132771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109301, d132771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d109302 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109302, d132772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109302, d132772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d109303 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109304 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro27297 (p : Pattern) (ha : d109310 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109305 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27296 q ha hb
    | true =>
      simp only [d109305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109306 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109307 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109308 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109309 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109310 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27298 (p : Pattern) (ha : d109316 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109311 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27297 q ha hb
    | true =>
      simp only [d109311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109312 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109313 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109314 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109315 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109316 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27299 (p : Pattern) (ha : d109322 p = 1) (hb : d132772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109317 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27298 q ha hb
    | true =>
      simp only [d109317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109318 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109319 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109320 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109321 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109322 q = 1) (hb : d132772 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27300 (p : Pattern) (ha : d10654 p = 1) (hb : d125748 p = 1) : d125750 p = 1 := by
  have h0 (q : Pattern) (ha : d10651 q = 1) (hb : d85721 q = 1) : d10651 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10652 q = 1) (hb : d125746 q = 1) : d10863 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d125746, d10863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10652, d125746, d10863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d34 q = 1) (hb : d125747 q = 1) : d34 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10653 q = 1) (hb : d125748 q = 1) : d125749 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10653, d125748, d125749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10653, d125748, d125749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10654 q = 1) (hb : d125748 q = 1) : d125750 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10654, d125750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10654, d125750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27301 (p : Pattern) (ha : d10660 p = 1) (hb : d125748 p = 1) : d125756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27300 q ha hb
    | true =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d125748 q = 1) : d125754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10659 q = 1) (hb : d125748 q = 1) : d125755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10659, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10660 q = 1) (hb : d125748 q = 1) : d125756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10660, d125756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10660, d125756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27302 (p : Pattern) (ha : d108784 p = 1) (hb : d125748 p = 1) : d125762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d125748 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d125748 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d125748 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10661 q = 1) (hb : d125748 q = 1) : d125757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27301 q ha hb
    | true =>
      simp only [d10661, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108780 q = 1) (hb : d125748 q = 1) : d125758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108780, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d125748 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108781 q = 1) (hb : d125748 q = 1) : d125759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108781, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108782 q = 1) (hb : d125748 q = 1) : d125760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108782, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108783 q = 1) (hb : d125748 q = 1) : d125761 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108783, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108784 q = 1) (hb : d125748 q = 1) : d125762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108784, d125762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108784, d125762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro27303 (p : Pattern) (ha : d10667 p = 1) (hb : d125748 p = 1) : d125763 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27300 q ha hb
    | true =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d125748 q = 1) : d125754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10659 q = 1) (hb : d125748 q = 1) : d125755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10659, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10667 q = 1) (hb : d125748 q = 1) : d125763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10667, d125763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10667, d125763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27304 (p : Pattern) (ha : d108789 p = 1) (hb : d125748 p = 1) : d125769 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d125748 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d125748 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d125748 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10661 q = 1) (hb : d125748 q = 1) : d125757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27301 q ha hb
    | true =>
      simp only [d10661, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108780 q = 1) (hb : d125748 q = 1) : d125758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108780, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d125748 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d108781 q = 1) (hb : d125748 q = 1) : d125759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108781, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108782 q = 1) (hb : d125748 q = 1) : d125760 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108782, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108783 q = 1) (hb : d125748 q = 1) : d125761 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108783, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d125748 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d125748 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d125748 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d10668 q = 1) (hb : d125748 q = 1) : d125764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27303 q ha hb
    | true =>
      simp only [d10668, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d108785 q = 1) (hb : d125748 q = 1) : d125765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108785, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d125748 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d108786 q = 1) (hb : d125748 q = 1) : d125766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108786, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108787 q = 1) (hb : d125748 q = 1) : d125767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108787, d125767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108787, d125767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108788 q = 1) (hb : d125748 q = 1) : d125768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108788, d125768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108788, d125768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d108789 q = 1) (hb : d125748 q = 1) : d125769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108789, d125769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108789, d125769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro27305 (p : Pattern) (ha : d108796 p = 1) (hb : d125748 p = 1) : d125776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d125748 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10668 q = 1) (hb : d125748 q = 1) : d125764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27303 q ha hb
    | true =>
      simp only [d10668, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108785 q = 1) (hb : d125748 q = 1) : d125765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108785, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d125748 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108786 q = 1) (hb : d125748 q = 1) : d125766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108786, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108794 q = 1) (hb : d125748 q = 1) : d125774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108794, d125774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108794, d125774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108795 q = 1) (hb : d125748 q = 1) : d125775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108795, d125775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108795, d125775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108796 q = 1) (hb : d125748 q = 1) : d125776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108796, d125776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108796, d125776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27306 (p : Pattern) (ha : d10691 p = 1) (hb : d125748 p = 1) : d125783 p = 1 := by
  have h0 (q : Pattern) (ha : d10688 q = 1) (hb : d85721 q = 1) : d10688 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10689 q = 1) (hb : d125746 q = 1) : d11021 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d125746, d11021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10689, d125746, d11021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d75 q = 1) (hb : d125747 q = 1) : d75 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10690 q = 1) (hb : d125748 q = 1) : d125782 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10690, d125748, d125782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10690, d125748, d125782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10691 q = 1) (hb : d125748 q = 1) : d125783 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10691, d125783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10691, d125783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27307 (p : Pattern) (ha : d10697 p = 1) (hb : d125748 p = 1) : d125789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d125748 q = 1) : d125784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27306 q ha hb
    | true =>
      simp only [d10692, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d125748 q = 1) : d125785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d125748 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10694 q = 1) (hb : d125748 q = 1) : d125786 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10694, d125786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10694, d125786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10695 q = 1) (hb : d125748 q = 1) : d125787 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10695, d125787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10695, d125787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10696 q = 1) (hb : d125748 q = 1) : d125788 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10696, d125788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10696, d125788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10697 q = 1) (hb : d125748 q = 1) : d125789 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10697, d125789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10697, d125789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27308 (p : Pattern) (ha : d108806 p = 1) (hb : d125748 p = 1) : d125795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d125748 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10698 q = 1) (hb : d125748 q = 1) : d125790 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d125790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27307 q ha hb
    | true =>
      simp only [d10698, d125790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108802 q = 1) (hb : d125748 q = 1) : d125791 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108802, d125791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108802, d125791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d125748 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108803 q = 1) (hb : d125748 q = 1) : d125792 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108803, d125792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108803, d125792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108804 q = 1) (hb : d125748 q = 1) : d125793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108804, d125793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108804, d125793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108805 q = 1) (hb : d125748 q = 1) : d125794 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108805, d125794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108805, d125794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108806 q = 1) (hb : d125748 q = 1) : d125795 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108806, d125795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108806, d125795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27309 (p : Pattern) (ha : d108812 p = 1) (hb : d125748 p = 1) : d125801 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d125748 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108790 q = 1) (hb : d125748 q = 1) : d125770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108790, d125770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27302 q ha hb
    | true =>
      simp only [d108790, d125770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27304 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d125748 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d108791 q = 1) (hb : d125748 q = 1) : d125771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108791, d125771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108791, d125771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108792 q = 1) (hb : d125748 q = 1) : d125772 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108792, d125772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108792, d125772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108793 q = 1) (hb : d125748 q = 1) : d125773 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108793, d125773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108793, d125773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108797 q = 1) (hb : d125748 q = 1) : d125777 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108797, d125777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108797, d125777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27305 q ha hb
  have h8 (q : Pattern) (ha : d108798 q = 1) (hb : d125748 q = 1) : d125778 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108798, d125778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108798, d125778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d108799 q = 1) (hb : d125748 q = 1) : d125779 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108799, d125779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108799, d125779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d108800 q = 1) (hb : d125748 q = 1) : d125780 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108800, d125780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108800, d125780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d108801 q = 1) (hb : d125748 q = 1) : d125781 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108801, d125781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108801, d125781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108807 q = 1) (hb : d125748 q = 1) : d125796 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108807, d125796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108807, d125796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27308 q ha hb
  have h13 (q : Pattern) (ha : d108808 q = 1) (hb : d125748 q = 1) : d125797 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108808, d125797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108808, d125797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d108809 q = 1) (hb : d125748 q = 1) : d125798 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108809, d125798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108809, d125798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d108810 q = 1) (hb : d125748 q = 1) : d125799 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108810, d125799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108810, d125799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d108811 q = 1) (hb : d125748 q = 1) : d125800 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108811, d125800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108811, d125800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d108812 q = 1) (hb : d125748 q = 1) : d125801 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108812, d125801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108812, d125801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro27310 (p : Pattern) (ha : d10719 p = 1) (hb : d125748 p = 1) : d125811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d125748 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d125748 q = 1) : d125757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27301 q ha hb
    | true =>
      simp only [d10661, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d125748 q = 1) : d125807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d125748 q = 1) : d125808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d125748 q = 1) : d125809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d125748 q = 1) : d125810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10719 q = 1) (hb : d125748 q = 1) : d125811 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d125811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10719, d125811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27311 (p : Pattern) (ha : d10726 p = 1) (hb : d125748 p = 1) : d125818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d125748 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d125748 q = 1) : d125757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27301 q ha hb
    | true =>
      simp only [d10661, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d125748 q = 1) : d125807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d125748 q = 1) : d125808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d125748 q = 1) : d125809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d125748 q = 1) : d125810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d125748 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10668 q = 1) (hb : d125748 q = 1) : d125764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27303 q ha hb
    | true =>
      simp only [d10668, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10722 q = 1) (hb : d125748 q = 1) : d125814 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10723 q = 1) (hb : d125748 q = 1) : d125815 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10723, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10724 q = 1) (hb : d125748 q = 1) : d125816 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10725 q = 1) (hb : d125748 q = 1) : d125817 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10726 q = 1) (hb : d125748 q = 1) : d125818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d125818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10726, d125818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro27312 (p : Pattern) (ha : d10801 p = 1) (hb : d125748 p = 1) : d125875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d125748 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10661 q = 1) (hb : d125748 q = 1) : d125757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27301 q ha hb
    | true =>
      simp only [d10661, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10715 q = 1) (hb : d125748 q = 1) : d125807 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10716 q = 1) (hb : d125748 q = 1) : d125808 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10716, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10717 q = 1) (hb : d125748 q = 1) : d125809 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10718 q = 1) (hb : d125748 q = 1) : d125810 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d125748 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10801 q = 1) (hb : d125748 q = 1) : d125875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10801, d125875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10801, d125875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27313 (p : Pattern) (ha : d10731 p = 1) (hb : d125748 p = 1) : d125823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27300 q ha hb
    | true =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d125748 q = 1) : d125754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10730 q = 1) (hb : d125748 q = 1) : d125822 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10731 q = 1) (hb : d125748 q = 1) : d125823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10731, d125823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10731, d125823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27314 (p : Pattern) (ha : d10738 p = 1) (hb : d125748 p = 1) : d125830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27300 q ha hb
    | true =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10736 q = 1) (hb : d125748 q = 1) : d125828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10737 q = 1) (hb : d125748 q = 1) : d125829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10737, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10738 q = 1) (hb : d125748 q = 1) : d125830 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10738, d125830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10738, d125830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27315 (p : Pattern) (ha : d10747 p = 1) (hb : d125748 p = 1) : d125836 p = 1 := by
  have h0 (q : Pattern) (ha : d10744 q = 1) (hb : d85721 q = 1) : d10744 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10745 q = 1) (hb : d125746 q = 1) : d125834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d125746, d125834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10745, d125746, d125834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10649 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10650 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10651 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10652 q = 1) (hb : d125747 q = 1) : d88341 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d125747, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10652, d125747, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d10746 q = 1) (hb : d125748 q = 1) : d125835 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10746, d125748, d125835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10746, d125748, d125835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10747 q = 1) (hb : d125748 q = 1) : d125836 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10747, d125836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10747, d125836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27316 (p : Pattern) (ha : d10753 p = 1) (hb : d125748 p = 1) : d125842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27315 q ha hb
    | true =>
      simp only [d10748, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27300 q ha hb
    | true =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d125748 q = 1) : d125839 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d125748 q = 1) : d125840 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d125748 q = 1) : d125841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10753 q = 1) (hb : d125748 q = 1) : d125842 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10753, d125842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10753, d125842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27317 (p : Pattern) (ha : d10772 p = 1) (hb : d125748 p = 1) : d125848 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27300 q ha hb
    | true =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d125748 q = 1) : d125845 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d125748 q = 1) : d125846 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d125748 q = 1) : d125847 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10772 q = 1) (hb : d125748 q = 1) : d125848 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10772, d125848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10772, d125848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27318 (p : Pattern) (ha : d108822 p = 1) (hb : d125748 p = 1) : d125854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d125748 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10732 q = 1) (hb : d125748 q = 1) : d125824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27313 q ha hb
    | true =>
      simp only [d10732, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10733 q = 1) (hb : d125748 q = 1) : d125825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10734 q = 1) (hb : d125748 q = 1) : d125826 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10734, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10735 q = 1) (hb : d125748 q = 1) : d125827 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d125748 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10739 q = 1) (hb : d125748 q = 1) : d125831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27314 q ha hb
    | true =>
      simp only [d10739, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10740 q = 1) (hb : d125748 q = 1) : d125832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10741 q = 1) (hb : d125748 q = 1) : d125833 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10741, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10754 q = 1) (hb : d125748 q = 1) : d125843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27316 q ha hb
    | true =>
      simp only [d10754, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27301 q ha hb
  have h11 (q : Pattern) (ha : d108818 q = 1) (hb : d125748 q = 1) : d125844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108818, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10773 q = 1) (hb : d125748 q = 1) : d125849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27317 q ha hb
    | true =>
      simp only [d10773, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10774 q = 1) (hb : d125748 q = 1) : d125850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10774, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108819 q = 1) (hb : d125748 q = 1) : d125851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108819, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108820 q = 1) (hb : d125748 q = 1) : d125852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108820, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108821 q = 1) (hb : d125748 q = 1) : d125853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108821, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108822 q = 1) (hb : d125748 q = 1) : d125854 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108822, d125854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108822, d125854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro27319 (p : Pattern) (ha : d10779 p = 1) (hb : d125748 p = 1) : d125855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27300 q ha hb
    | true =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10658 q = 1) (hb : d125748 q = 1) : d125754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10730 q = 1) (hb : d125748 q = 1) : d125822 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10779 q = 1) (hb : d125748 q = 1) : d125855 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10779, d125855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10779, d125855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27320 (p : Pattern) (ha : d10784 p = 1) (hb : d125748 p = 1) : d125860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27300 q ha hb
    | true =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d125748 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d125748 q = 1) : d125753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10736 q = 1) (hb : d125748 q = 1) : d125828 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10737 q = 1) (hb : d125748 q = 1) : d125829 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10737, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10784 q = 1) (hb : d125748 q = 1) : d125860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10784, d125860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10784, d125860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27321 (p : Pattern) (ha : d10788 p = 1) (hb : d125748 p = 1) : d125864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27315 q ha hb
    | true =>
      simp only [d10748, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27300 q ha hb
    | true =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d125748 q = 1) : d125839 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d125748 q = 1) : d125840 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d125748 q = 1) : d125841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10788 q = 1) (hb : d125748 q = 1) : d125864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10788, d125864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10788, d125864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27322 (p : Pattern) (ha : d10793 p = 1) (hb : d125748 p = 1) : d125867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d125748 q = 1) : d125751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27300 q ha hb
    | true =>
      simp only [d10655, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d125748 q = 1) : d125752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d125748 q = 1) : d125845 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d125748 q = 1) : d125846 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d125748 q = 1) : d125847 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10793 q = 1) (hb : d125748 q = 1) : d125867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10793, d125867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10793, d125867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27323 (p : Pattern) (ha : d108827 p = 1) (hb : d125748 p = 1) : d125873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d125748 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10732 q = 1) (hb : d125748 q = 1) : d125824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27313 q ha hb
    | true =>
      simp only [d10732, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10733 q = 1) (hb : d125748 q = 1) : d125825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10734 q = 1) (hb : d125748 q = 1) : d125826 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10734, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10735 q = 1) (hb : d125748 q = 1) : d125827 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d125748 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10739 q = 1) (hb : d125748 q = 1) : d125831 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27314 q ha hb
    | true =>
      simp only [d10739, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10740 q = 1) (hb : d125748 q = 1) : d125832 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10741 q = 1) (hb : d125748 q = 1) : d125833 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10741, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10754 q = 1) (hb : d125748 q = 1) : d125843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27316 q ha hb
    | true =>
      simp only [d10754, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27301 q ha hb
  have h11 (q : Pattern) (ha : d108818 q = 1) (hb : d125748 q = 1) : d125844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108818, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108818, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10773 q = 1) (hb : d125748 q = 1) : d125849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27317 q ha hb
    | true =>
      simp only [d10773, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10774 q = 1) (hb : d125748 q = 1) : d125850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10774, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108819 q = 1) (hb : d125748 q = 1) : d125851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108819, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108819, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108820 q = 1) (hb : d125748 q = 1) : d125852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108820, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108820, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108821 q = 1) (hb : d125748 q = 1) : d125853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108821, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108821, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d125748 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10780 q = 1) (hb : d125748 q = 1) : d125856 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10780, d125856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27319 q ha hb
    | true =>
      simp only [d10780, d125856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10781 q = 1) (hb : d125748 q = 1) : d125857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10781, d125857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10781, d125857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10782 q = 1) (hb : d125748 q = 1) : d125858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10782, d125858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10782, d125858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10783 q = 1) (hb : d125748 q = 1) : d125859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10783, d125859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10783, d125859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d125748 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d10785 q = 1) (hb : d125748 q = 1) : d125861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10785, d125861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27320 q ha hb
    | true =>
      simp only [d10785, d125861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10786 q = 1) (hb : d125748 q = 1) : d125862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10786, d125862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10786, d125862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10787 q = 1) (hb : d125748 q = 1) : d125863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10787, d125863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10787, d125863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d10789 q = 1) (hb : d125748 q = 1) : d125865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d125865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27321 q ha hb
    | true =>
      simp only [d10789, d125865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27303 q ha hb
  have h27 (q : Pattern) (ha : d108823 q = 1) (hb : d125748 q = 1) : d125866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d125866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108823, d125866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d10794 q = 1) (hb : d125748 q = 1) : d125868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d125868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27322 q ha hb
    | true =>
      simp only [d10794, d125868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d10795 q = 1) (hb : d125748 q = 1) : d125869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d125869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d10795, d125869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d108824 q = 1) (hb : d125748 q = 1) : d125870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d125870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108824, d125870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108825 q = 1) (hb : d125748 q = 1) : d125871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108825, d125871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108825, d125871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d108826 q = 1) (hb : d125748 q = 1) : d125872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108826, d125872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108826, d125872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d108827 q = 1) (hb : d125748 q = 1) : d125873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108827, d125873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108827, d125873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro27324 (p : Pattern) (ha : d108834 p = 1) (hb : d125748 p = 1) : d125882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10789 q = 1) (hb : d125748 q = 1) : d125865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d125865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27321 q ha hb
    | true =>
      simp only [d10789, d125865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27303 q ha hb
  have h2 (q : Pattern) (ha : d108823 q = 1) (hb : d125748 q = 1) : d125866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108823, d125866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108823, d125866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10794 q = 1) (hb : d125748 q = 1) : d125868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d125868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27322 q ha hb
    | true =>
      simp only [d10794, d125868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10795 q = 1) (hb : d125748 q = 1) : d125869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d125869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10795, d125869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108824 q = 1) (hb : d125748 q = 1) : d125870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108824, d125870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108824, d125870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108832 q = 1) (hb : d125748 q = 1) : d125880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108832, d125880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108832, d125880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108833 q = 1) (hb : d125748 q = 1) : d125881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108833, d125881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108833, d125881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108834 q = 1) (hb : d125748 q = 1) : d125882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108834, d125882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108834, d125882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27325 (p : Pattern) (ha : d10819 p = 1) (hb : d125748 p = 1) : d125890 p = 1 := by
  have h0 (q : Pattern) (ha : d10816 q = 1) (hb : d85721 q = 1) : d10816 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10817 q = 1) (hb : d125746 q = 1) : d125888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d125746, d125888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10817, d125746, d125888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10686 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10687 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10688 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10689 q = 1) (hb : d125747 q = 1) : d88405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d125747, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10689, d125747, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d10818 q = 1) (hb : d125748 q = 1) : d125889 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10818, d125748, d125889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10818, d125748, d125889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10819 q = 1) (hb : d125748 q = 1) : d125890 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10819, d125890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10819, d125890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27326 (p : Pattern) (ha : d10825 p = 1) (hb : d125748 p = 1) : d125896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10820 q = 1) (hb : d125748 q = 1) : d125891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10820, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27325 q ha hb
    | true =>
      simp only [d10820, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10821 q = 1) (hb : d125748 q = 1) : d125892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10821, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10821, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10692 q = 1) (hb : d125748 q = 1) : d125784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27306 q ha hb
    | true =>
      simp only [d10692, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10693 q = 1) (hb : d125748 q = 1) : d125785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10822 q = 1) (hb : d125748 q = 1) : d125893 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10822, d125893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10822, d125893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10823 q = 1) (hb : d125748 q = 1) : d125894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10823, d125894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10823, d125894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10824 q = 1) (hb : d125748 q = 1) : d125895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10824, d125895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10824, d125895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10825 q = 1) (hb : d125748 q = 1) : d125896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10825, d125896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10825, d125896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27327 (p : Pattern) (ha : d10844 p = 1) (hb : d125748 p = 1) : d125902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d125748 q = 1) : d125784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27306 q ha hb
    | true =>
      simp only [d10692, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d125748 q = 1) : d125785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10841 q = 1) (hb : d125748 q = 1) : d125899 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10841, d125899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10841, d125899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10842 q = 1) (hb : d125748 q = 1) : d125900 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10842, d125900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10842, d125900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10843 q = 1) (hb : d125748 q = 1) : d125901 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10843, d125901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10843, d125901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10844 q = 1) (hb : d125748 q = 1) : d125902 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10844, d125902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10844, d125902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27328 (p : Pattern) (ha : d108844 p = 1) (hb : d125748 p = 1) : d125908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10826 q = 1) (hb : d125748 q = 1) : d125897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10826, d125897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27326 q ha hb
    | true =>
      simp only [d10826, d125897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27307 q ha hb
  have h2 (q : Pattern) (ha : d108840 q = 1) (hb : d125748 q = 1) : d125898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108840, d125898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108840, d125898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10845 q = 1) (hb : d125748 q = 1) : d125903 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10845, d125903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27327 q ha hb
    | true =>
      simp only [d10845, d125903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10846 q = 1) (hb : d125748 q = 1) : d125904 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10846, d125904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10846, d125904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108841 q = 1) (hb : d125748 q = 1) : d125905 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108841, d125905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108841, d125905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108842 q = 1) (hb : d125748 q = 1) : d125906 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108842, d125906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108842, d125906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108843 q = 1) (hb : d125748 q = 1) : d125907 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108843, d125907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108843, d125907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108844 q = 1) (hb : d125748 q = 1) : d125908 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108844, d125908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108844, d125908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27329 (p : Pattern) (ha : d108850 p = 1) (hb : d125748 p = 1) : d125914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10720 q = 1) (hb : d125748 q = 1) : d125812 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10720, d125812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10720, d125812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27310 q ha hb
  have h2 (q : Pattern) (ha : d10721 q = 1) (hb : d125748 q = 1) : d125813 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10721, d125813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10721, d125813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10727 q = 1) (hb : d125748 q = 1) : d125819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d125819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27310 q ha hb
    | true =>
      simp only [d10727, d125819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27311 q ha hb
  have h4 (q : Pattern) (ha : d10728 q = 1) (hb : d125748 q = 1) : d125820 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d125820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10728, d125820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10729 q = 1) (hb : d125748 q = 1) : d125821 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10729, d125821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10729, d125821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108828 q = 1) (hb : d125748 q = 1) : d125874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108828, d125874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27318 q ha hb
    | true =>
      simp only [d108828, d125874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27323 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d125748 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10802 q = 1) (hb : d125748 q = 1) : d125876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10802, d125876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27312 q ha hb
    | true =>
      simp only [d10802, d125876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108829 q = 1) (hb : d125748 q = 1) : d125877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108829, d125877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108829, d125877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108830 q = 1) (hb : d125748 q = 1) : d125878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108830, d125878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108830, d125878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d108831 q = 1) (hb : d125748 q = 1) : d125879 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108831, d125879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108831, d125879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108835 q = 1) (hb : d125748 q = 1) : d125883 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108835, d125883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108835, d125883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27324 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d125748 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d108836 q = 1) (hb : d125748 q = 1) : d125884 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108836, d125884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108836, d125884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108837 q = 1) (hb : d125748 q = 1) : d125885 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108837, d125885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108837, d125885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108838 q = 1) (hb : d125748 q = 1) : d125886 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108838, d125886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108838, d125886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d108839 q = 1) (hb : d125748 q = 1) : d125887 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108839, d125887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108839, d125887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108845 q = 1) (hb : d125748 q = 1) : d125909 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108845, d125909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108845, d125909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27328 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d125748 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d108846 q = 1) (hb : d125748 q = 1) : d125910 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108846, d125910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108846, d125910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d108847 q = 1) (hb : d125748 q = 1) : d125911 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108847, d125911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108847, d125911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108848 q = 1) (hb : d125748 q = 1) : d125912 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108848, d125912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108848, d125912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108849 q = 1) (hb : d125748 q = 1) : d125913 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108849, d125913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108849, d125913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d108850 q = 1) (hb : d125748 q = 1) : d125914 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108850, d125914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108850, d125914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro27330 (p : Pattern) (ha : d108856 p = 1) (hb : d125748 p = 1) : d125920 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d125748 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108813 q = 1) (hb : d125748 q = 1) : d125802 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108813, d125802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108813, d125802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27309 q ha hb
  have h3 (q : Pattern) (ha : d108814 q = 1) (hb : d125748 q = 1) : d125803 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108814, d125803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108814, d125803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108815 q = 1) (hb : d125748 q = 1) : d125804 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108815, d125804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108815, d125804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108816 q = 1) (hb : d125748 q = 1) : d125805 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108816, d125805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108816, d125805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108817 q = 1) (hb : d125748 q = 1) : d125806 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108817, d125806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108817, d125806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108851 q = 1) (hb : d125748 q = 1) : d125915 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108851, d125915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108851, d125915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27329 q ha hb
  have h8 (q : Pattern) (ha : d108852 q = 1) (hb : d125748 q = 1) : d125916 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108852, d125916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108852, d125916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108853 q = 1) (hb : d125748 q = 1) : d125917 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108853, d125917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108853, d125917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108854 q = 1) (hb : d125748 q = 1) : d125918 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108854, d125918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108854, d125918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d108855 q = 1) (hb : d125748 q = 1) : d125919 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108855, d125919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108855, d125919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108856 q = 1) (hb : d125748 q = 1) : d125920 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108856, d125920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108856, d125920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27331 (p : Pattern) (ha : d10865 p = 1) (hb : d125748 p = 1) : d125836 p = 1 := by
  have h0 (q : Pattern) (ha : d10744 q = 1) (hb : d85721 q = 1) : d10744 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10745 q = 1) (hb : d125746 q = 1) : d125834 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d125746, d125834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10745, d125746, d125834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10649 q = 1) (hb : d112686 q = 1) : d88338 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12423 q ha hb
    | true =>
      simp only [d10649, d112686, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10650 q = 1) (hb : d112686 q = 1) : d88339 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10650, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10651 q = 1) (hb : d112686 q = 1) : d88340 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10651, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10863 q = 1) (hb : d125747 q = 1) : d88341 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d125747, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10863, d125747, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d10864 q = 1) (hb : d125748 q = 1) : d125835 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10864, d125748, d125835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10864, d125748, d125835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d10865 q = 1) (hb : d125748 q = 1) : d125836 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10865, d125836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10865, d125836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27332 (p : Pattern) (ha : d10875 p = 1) (hb : d125748 p = 1) : d125924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27331 q ha hb
    | true =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10873 q = 1) (hb : d125748 q = 1) : d125922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10873, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10874 q = 1) (hb : d125748 q = 1) : d125923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10874, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10875 q = 1) (hb : d125748 q = 1) : d125924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10875, d125924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10875, d125924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27333 (p : Pattern) (ha : d10885 p = 1) (hb : d125748 p = 1) : d125930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10879 q = 1) (hb : d125748 q = 1) : d10879 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10880 q = 1) (hb : d125748 q = 1) : d125925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27332 q ha hb
    | true =>
      simp only [d10880, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10881 q = 1) (hb : d125748 q = 1) : d125926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10882 q = 1) (hb : d125748 q = 1) : d125927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10882, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10883 q = 1) (hb : d125748 q = 1) : d125928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10884 q = 1) (hb : d125748 q = 1) : d125929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10885 q = 1) (hb : d125748 q = 1) : d125930 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d125930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10885, d125930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27334 (p : Pattern) (ha : d10888 p = 1) (hb : d125748 p = 1) : d125933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27331 q ha hb
    | true =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10873 q = 1) (hb : d125748 q = 1) : d125922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10873, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10874 q = 1) (hb : d125748 q = 1) : d125923 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10874, d125923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10888 q = 1) (hb : d125748 q = 1) : d125933 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10888, d125933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10888, d125933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27335 (p : Pattern) (ha : d10895 p = 1) (hb : d125748 p = 1) : d125939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10879 q = 1) (hb : d125748 q = 1) : d10879 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10880 q = 1) (hb : d125748 q = 1) : d125925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27332 q ha hb
    | true =>
      simp only [d10880, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10881 q = 1) (hb : d125748 q = 1) : d125926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10882 q = 1) (hb : d125748 q = 1) : d125927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10882, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10883 q = 1) (hb : d125748 q = 1) : d125928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10884 q = 1) (hb : d125748 q = 1) : d125929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10889 q = 1) (hb : d125748 q = 1) : d10889 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10890 q = 1) (hb : d125748 q = 1) : d125934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d125934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27334 q ha hb
    | true =>
      simp only [d10890, d125934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10891 q = 1) (hb : d125748 q = 1) : d125935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d125935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10892 q = 1) (hb : d125748 q = 1) : d125936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10892, d125936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10893 q = 1) (hb : d125748 q = 1) : d125937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d125937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10894 q = 1) (hb : d125748 q = 1) : d125938 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d125938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10895 q = 1) (hb : d125748 q = 1) : d125939 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d125939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10895, d125939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro27336 (p : Pattern) (ha : d10992 p = 1) (hb : d125748 p = 1) : d125997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10879 q = 1) (hb : d125748 q = 1) : d10879 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10880 q = 1) (hb : d125748 q = 1) : d125925 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27332 q ha hb
    | true =>
      simp only [d10880, d125925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10881 q = 1) (hb : d125748 q = 1) : d125926 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d125926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10882 q = 1) (hb : d125748 q = 1) : d125927 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10882, d125927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10883 q = 1) (hb : d125748 q = 1) : d125928 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d125928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10884 q = 1) (hb : d125748 q = 1) : d125929 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d125929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10991 q = 1) (hb : d125748 q = 1) : d10991 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10992 q = 1) (hb : d125748 q = 1) : d125997 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10992, d125997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10992, d125997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27337 (p : Pattern) (ha : d10900 p = 1) (hb : d125748 p = 1) : d125944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27331 q ha hb
    | true =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10873 q = 1) (hb : d125748 q = 1) : d125922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10873, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10899 q = 1) (hb : d125748 q = 1) : d125943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d125943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d125943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10900 q = 1) (hb : d125748 q = 1) : d125944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10900, d125944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10900, d125944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27338 (p : Pattern) (ha : d10909 p = 1) (hb : d125748 p = 1) : d125951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27331 q ha hb
    | true =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10907 q = 1) (hb : d125748 q = 1) : d125949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d125949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d125949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10908 q = 1) (hb : d125748 q = 1) : d125950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d125950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10908, d125950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10909 q = 1) (hb : d125748 q = 1) : d125951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10909, d125951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10909, d125951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27339 (p : Pattern) (ha : d10921 p = 1) (hb : d125748 p = 1) : d125958 p = 1 := by
  have h0 (q : Pattern) (ha : d10918 q = 1) (hb : d85721 q = 1) : d10918 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10744 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10919 q = 1) (hb : d125746 q = 1) : d125955 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10919, d125746, d125955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10919, d125746, d125955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10742 q = 1) (hb : d112686 q = 1) : d114306 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12463 q ha hb
    | true =>
      simp only [d10742, d112686, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10743 q = 1) (hb : d112686 q = 1) : d114307 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10743, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10744 q = 1) (hb : d112686 q = 1) : d114308 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10744, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10651 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10745 q = 1) (hb : d125747 q = 1) : d125956 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d125747, d125956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10745, d125747, d125956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d10920 q = 1) (hb : d125748 q = 1) : d125957 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10920, d125748, d125957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10920, d125748, d125957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d10921 q = 1) (hb : d125748 q = 1) : d125958 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10921, d125958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10921, d125958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27340 (p : Pattern) (ha : d10927 p = 1) (hb : d125748 p = 1) : d125964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d125748 q = 1) : d125959 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d125959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27339 q ha hb
    | true =>
      simp only [d10922, d125959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d125748 q = 1) : d125960 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d125960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d125960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27331 q ha hb
    | true =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d125748 q = 1) : d125961 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d125961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d125961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d125748 q = 1) : d125962 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d125962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d125962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d125748 q = 1) : d125963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d125963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d125963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10927 q = 1) (hb : d125748 q = 1) : d125964 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10927, d125964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10927, d125964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27341 (p : Pattern) (ha : d10955 p = 1) (hb : d125748 p = 1) : d125970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27331 q ha hb
    | true =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d125748 q = 1) : d125967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d125967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d125967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d125748 q = 1) : d125968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d125968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d125968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d125748 q = 1) : d125969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d125969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d125969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10955 q = 1) (hb : d125748 q = 1) : d125970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10955, d125970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10955, d125970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27342 (p : Pattern) (ha : d108861 p = 1) (hb : d125748 p = 1) : d125976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10902 q = 1) (hb : d125748 q = 1) : d10902 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10903 q = 1) (hb : d125748 q = 1) : d125945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d125945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27337 q ha hb
    | true =>
      simp only [d10903, d125945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10904 q = 1) (hb : d125748 q = 1) : d125946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d125946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d125946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10905 q = 1) (hb : d125748 q = 1) : d125947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d125947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10905, d125947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10906 q = 1) (hb : d125748 q = 1) : d125948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d125948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d125948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10912 q = 1) (hb : d125748 q = 1) : d10912 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10913 q = 1) (hb : d125748 q = 1) : d125952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d125952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27338 q ha hb
    | true =>
      simp only [d10913, d125952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10914 q = 1) (hb : d125748 q = 1) : d125953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d125953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d125953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10915 q = 1) (hb : d125748 q = 1) : d125954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d125954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10915, d125954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10928 q = 1) (hb : d125748 q = 1) : d125965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d125965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27340 q ha hb
    | true =>
      simp only [d10928, d125965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27332 q ha hb
  have h11 (q : Pattern) (ha : d108857 q = 1) (hb : d125748 q = 1) : d125966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d125966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108857, d125966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10956 q = 1) (hb : d125748 q = 1) : d125971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d125971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27341 q ha hb
    | true =>
      simp only [d10956, d125971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10957 q = 1) (hb : d125748 q = 1) : d125972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d125972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10957, d125972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108858 q = 1) (hb : d125748 q = 1) : d125973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d125973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108858, d125973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108859 q = 1) (hb : d125748 q = 1) : d125974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d125974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108859, d125974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108860 q = 1) (hb : d125748 q = 1) : d125975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d125975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108860, d125975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108861 q = 1) (hb : d125748 q = 1) : d125976 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108861, d125976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108861, d125976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro27343 (p : Pattern) (ha : d10962 p = 1) (hb : d125748 p = 1) : d125977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27331 q ha hb
    | true =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10873 q = 1) (hb : d125748 q = 1) : d125922 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10873, d125922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10899 q = 1) (hb : d125748 q = 1) : d125943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d125943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d125943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10962 q = 1) (hb : d125748 q = 1) : d125977 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10962, d125977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10962, d125977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27344 (p : Pattern) (ha : d10968 p = 1) (hb : d125748 p = 1) : d125982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27331 q ha hb
    | true =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10871 q = 1) (hb : d125748 q = 1) : d10871 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10872 q = 1) (hb : d125748 q = 1) : d125921 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d125921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10907 q = 1) (hb : d125748 q = 1) : d125949 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d125949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d125949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10908 q = 1) (hb : d125748 q = 1) : d125950 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d125950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10908, d125950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10968 q = 1) (hb : d125748 q = 1) : d125982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10968, d125982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10968, d125982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27345 (p : Pattern) (ha : d10973 p = 1) (hb : d125748 p = 1) : d125986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d125748 q = 1) : d125959 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d125959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27339 q ha hb
    | true =>
      simp only [d10922, d125959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d125748 q = 1) : d125960 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d125960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d125960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27331 q ha hb
    | true =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d125748 q = 1) : d125961 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d125961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d125961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d125748 q = 1) : d125962 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d125962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d125962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d125748 q = 1) : d125963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d125963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d125963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10973 q = 1) (hb : d125748 q = 1) : d125986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10973, d125986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10973, d125986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27346 (p : Pattern) (ha : d10979 p = 1) (hb : d125748 p = 1) : d125989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d125748 q = 1) : d125837 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27331 q ha hb
    | true =>
      simp only [d10866, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d125748 q = 1) : d125838 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d125748 q = 1) : d125967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d125967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d125967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d125748 q = 1) : d125968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d125968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d125968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d125748 q = 1) : d125969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d125969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d125969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10979 q = 1) (hb : d125748 q = 1) : d125989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10979, d125989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10979, d125989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27347 (p : Pattern) (ha : d108866 p = 1) (hb : d125748 p = 1) : d125995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10902 q = 1) (hb : d125748 q = 1) : d10902 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10903 q = 1) (hb : d125748 q = 1) : d125945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d125945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27337 q ha hb
    | true =>
      simp only [d10903, d125945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10904 q = 1) (hb : d125748 q = 1) : d125946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d125946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d125946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10905 q = 1) (hb : d125748 q = 1) : d125947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d125947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10905, d125947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10906 q = 1) (hb : d125748 q = 1) : d125948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d125948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d125948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10912 q = 1) (hb : d125748 q = 1) : d10912 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10913 q = 1) (hb : d125748 q = 1) : d125952 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d125952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27338 q ha hb
    | true =>
      simp only [d10913, d125952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10914 q = 1) (hb : d125748 q = 1) : d125953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d125953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d125953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10915 q = 1) (hb : d125748 q = 1) : d125954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d125954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10915, d125954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10928 q = 1) (hb : d125748 q = 1) : d125965 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d125965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27340 q ha hb
    | true =>
      simp only [d10928, d125965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27332 q ha hb
  have h11 (q : Pattern) (ha : d108857 q = 1) (hb : d125748 q = 1) : d125966 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108857, d125966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108857, d125966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10956 q = 1) (hb : d125748 q = 1) : d125971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d125971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27341 q ha hb
    | true =>
      simp only [d10956, d125971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10957 q = 1) (hb : d125748 q = 1) : d125972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d125972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10957, d125972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108858 q = 1) (hb : d125748 q = 1) : d125973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108858, d125973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108858, d125973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108859 q = 1) (hb : d125748 q = 1) : d125974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108859, d125974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108859, d125974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108860 q = 1) (hb : d125748 q = 1) : d125975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108860, d125975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108860, d125975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10963 q = 1) (hb : d125748 q = 1) : d10963 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d10964 q = 1) (hb : d125748 q = 1) : d125978 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10964, d125978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27343 q ha hb
    | true =>
      simp only [d10964, d125978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d10965 q = 1) (hb : d125748 q = 1) : d125979 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10965, d125979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10965, d125979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10966 q = 1) (hb : d125748 q = 1) : d125980 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10966, d125980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10966, d125980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10967 q = 1) (hb : d125748 q = 1) : d125981 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10967, d125981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10967, d125981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10969 q = 1) (hb : d125748 q = 1) : d10969 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d10970 q = 1) (hb : d125748 q = 1) : d125983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10970, d125983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27344 q ha hb
    | true =>
      simp only [d10970, d125983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10971 q = 1) (hb : d125748 q = 1) : d125984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10971, d125984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10971, d125984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10972 q = 1) (hb : d125748 q = 1) : d125985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10972, d125985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d10972, d125985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d10974 q = 1) (hb : d125748 q = 1) : d125987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d125987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27345 q ha hb
    | true =>
      simp only [d10974, d125987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27334 q ha hb
  have h27 (q : Pattern) (ha : d108862 q = 1) (hb : d125748 q = 1) : d125988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d125988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108862, d125988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d10980 q = 1) (hb : d125748 q = 1) : d125990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d125990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27346 q ha hb
    | true =>
      simp only [d10980, d125990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d10981 q = 1) (hb : d125748 q = 1) : d125991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d125991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d10981, d125991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d108863 q = 1) (hb : d125748 q = 1) : d125992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d125992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108863, d125992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108864 q = 1) (hb : d125748 q = 1) : d125993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108864, d125993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108864, d125993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d108865 q = 1) (hb : d125748 q = 1) : d125994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108865, d125994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108865, d125994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d108866 q = 1) (hb : d125748 q = 1) : d125995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108866, d125995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108866, d125995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro27348 (p : Pattern) (ha : d108873 p = 1) (hb : d125748 p = 1) : d126004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10974 q = 1) (hb : d125748 q = 1) : d125987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d125987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27345 q ha hb
    | true =>
      simp only [d10974, d125987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27334 q ha hb
  have h2 (q : Pattern) (ha : d108862 q = 1) (hb : d125748 q = 1) : d125988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108862, d125988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108862, d125988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10980 q = 1) (hb : d125748 q = 1) : d125990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d125990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27346 q ha hb
    | true =>
      simp only [d10980, d125990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10981 q = 1) (hb : d125748 q = 1) : d125991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d125991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10981, d125991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108863 q = 1) (hb : d125748 q = 1) : d125992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108863, d125992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108863, d125992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108871 q = 1) (hb : d125748 q = 1) : d126002 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108871, d126002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108871, d126002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108872 q = 1) (hb : d125748 q = 1) : d126003 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108872, d126003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108872, d126003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108873 q = 1) (hb : d125748 q = 1) : d126004 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108873, d126004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108873, d126004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27349 (p : Pattern) (ha : d11018 p = 1) (hb : d125748 p = 1) : d126013 p = 1 := by
  have h0 (q : Pattern) (ha : d11015 q = 1) (hb : d85721 q = 1) : d11015 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10816 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11016 q = 1) (hb : d125746 q = 1) : d126010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11016, d125746, d126010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11016, d125746, d126010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10814 q = 1) (hb : d112686 q = 1) : d114363 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12479 q ha hb
    | true =>
      simp only [d10814, d112686, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10815 q = 1) (hb : d112686 q = 1) : d114364 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10815, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10816 q = 1) (hb : d112686 q = 1) : d114365 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10816, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10688 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10817 q = 1) (hb : d125747 q = 1) : d126011 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d125747, d126011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10817, d125747, d126011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d11017 q = 1) (hb : d125748 q = 1) : d126012 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11017, d125748, d126012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11017, d125748, d126012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11018 q = 1) (hb : d125748 q = 1) : d126013 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11018, d126013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11018, d126013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27350 (p : Pattern) (ha : d11023 p = 1) (hb : d125748 p = 1) : d125890 p = 1 := by
  have h0 (q : Pattern) (ha : d10816 q = 1) (hb : d85721 q = 1) : d10816 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10688 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10817 q = 1) (hb : d125746 q = 1) : d125888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d125746, d125888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10817, d125746, d125888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10686 q = 1) (hb : d112686 q = 1) : d88402 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12435 q ha hb
    | true =>
      simp only [d10686, d112686, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10687 q = 1) (hb : d112686 q = 1) : d88403 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10687, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10688 q = 1) (hb : d112686 q = 1) : d88404 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10688, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11021 q = 1) (hb : d125747 q = 1) : d88405 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d125747, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11021, d125747, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11022 q = 1) (hb : d125748 q = 1) : d125889 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11022, d125748, d125889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11022, d125748, d125889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11023 q = 1) (hb : d125748 q = 1) : d125890 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11023, d125890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11023, d125890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27351 (p : Pattern) (ha : d11029 p = 1) (hb : d125748 p = 1) : d126019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11019 q = 1) (hb : d125748 q = 1) : d126014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11019, d126014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27349 q ha hb
    | true =>
      simp only [d11019, d126014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11020 q = 1) (hb : d125748 q = 1) : d126015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11020, d126015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11020, d126015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11024 q = 1) (hb : d125748 q = 1) : d125891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27350 q ha hb
    | true =>
      simp only [d11024, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11025 q = 1) (hb : d125748 q = 1) : d125892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11026 q = 1) (hb : d125748 q = 1) : d126016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11026, d126016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11026, d126016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11027 q = 1) (hb : d125748 q = 1) : d126017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11027, d126017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11027, d126017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11028 q = 1) (hb : d125748 q = 1) : d126018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11028, d126018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11028, d126018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11029 q = 1) (hb : d125748 q = 1) : d126019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11029, d126019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11029, d126019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27352 (p : Pattern) (ha : d11037 p = 1) (hb : d125748 p = 1) : d126023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d125748 q = 1) : d125891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27350 q ha hb
    | true =>
      simp only [d11024, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d125748 q = 1) : d125892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11033 q = 1) (hb : d125748 q = 1) : d11033 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11034 q = 1) (hb : d125748 q = 1) : d126020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11034, d126020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11034, d126020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11035 q = 1) (hb : d125748 q = 1) : d126021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11035, d126021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11035, d126021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11036 q = 1) (hb : d125748 q = 1) : d126022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11036, d126022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11036, d126022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11037 q = 1) (hb : d125748 q = 1) : d126023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11037, d126023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11037, d126023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27353 (p : Pattern) (ha : d11065 p = 1) (hb : d125748 p = 1) : d126029 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d125748 q = 1) : d125891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27350 q ha hb
    | true =>
      simp only [d11024, d125891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d125748 q = 1) : d125892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d125892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11062 q = 1) (hb : d125748 q = 1) : d126026 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11062, d126026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11062, d126026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11063 q = 1) (hb : d125748 q = 1) : d126027 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11063, d126027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11063, d126027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11064 q = 1) (hb : d125748 q = 1) : d126028 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11064, d126028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11064, d126028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11065 q = 1) (hb : d125748 q = 1) : d126029 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11065, d126029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11065, d126029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27354 (p : Pattern) (ha : d108883 p = 1) (hb : d125748 p = 1) : d126035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11038 q = 1) (hb : d125748 q = 1) : d126024 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11038, d126024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27351 q ha hb
    | true =>
      simp only [d11038, d126024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27352 q ha hb
  have h2 (q : Pattern) (ha : d108879 q = 1) (hb : d125748 q = 1) : d126025 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108879, d126025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108879, d126025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11066 q = 1) (hb : d125748 q = 1) : d126030 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11066, d126030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27353 q ha hb
    | true =>
      simp only [d11066, d126030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11067 q = 1) (hb : d125748 q = 1) : d126031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11067, d126031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11067, d126031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108880 q = 1) (hb : d125748 q = 1) : d126032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108880, d126032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108880, d126032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108881 q = 1) (hb : d125748 q = 1) : d126033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108881, d126033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108881, d126033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108882 q = 1) (hb : d125748 q = 1) : d126034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108882, d126034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108882, d126034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108883 q = 1) (hb : d125748 q = 1) : d126035 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108883, d126035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108883, d126035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27355 (p : Pattern) (ha : d108889 p = 1) (hb : d125748 p = 1) : d126041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10886 q = 1) (hb : d125748 q = 1) : d125931 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10886, d125931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10886, d125931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27333 q ha hb
  have h2 (q : Pattern) (ha : d10887 q = 1) (hb : d125748 q = 1) : d125932 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10887, d125932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10887, d125932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10896 q = 1) (hb : d125748 q = 1) : d125940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27333 q ha hb
    | true =>
      simp only [d10896, d125940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27335 q ha hb
  have h4 (q : Pattern) (ha : d10897 q = 1) (hb : d125748 q = 1) : d125941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10897, d125941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10898 q = 1) (hb : d125748 q = 1) : d125942 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10898, d125942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10898, d125942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108867 q = 1) (hb : d125748 q = 1) : d125996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108867, d125996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27342 q ha hb
    | true =>
      simp only [d108867, d125996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27347 q ha hb
  have h7 (q : Pattern) (ha : d10998 q = 1) (hb : d125748 q = 1) : d10998 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10999 q = 1) (hb : d125748 q = 1) : d125998 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10999, d125998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27336 q ha hb
    | true =>
      simp only [d10999, d125998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108868 q = 1) (hb : d125748 q = 1) : d125999 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108868, d125999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108868, d125999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108869 q = 1) (hb : d125748 q = 1) : d126000 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108869, d126000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108869, d126000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d108870 q = 1) (hb : d125748 q = 1) : d126001 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108870, d126001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108870, d126001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108874 q = 1) (hb : d125748 q = 1) : d126005 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108874, d126005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108874, d126005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27348 q ha hb
  have h13 (q : Pattern) (ha : d11008 q = 1) (hb : d125748 q = 1) : d11008 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d108875 q = 1) (hb : d125748 q = 1) : d126006 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108875, d126006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108875, d126006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108876 q = 1) (hb : d125748 q = 1) : d126007 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108876, d126007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108876, d126007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108877 q = 1) (hb : d125748 q = 1) : d126008 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108877, d126008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108877, d126008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d108878 q = 1) (hb : d125748 q = 1) : d126009 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108878, d126009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108878, d126009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108884 q = 1) (hb : d125748 q = 1) : d126036 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108884, d126036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108884, d126036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27354 q ha hb
  have h19 (q : Pattern) (ha : d11083 q = 1) (hb : d125748 q = 1) : d11083 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d108885 q = 1) (hb : d125748 q = 1) : d126037 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108885, d126037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108885, d126037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d108886 q = 1) (hb : d125748 q = 1) : d126038 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108886, d126038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108886, d126038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108887 q = 1) (hb : d125748 q = 1) : d126039 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108887, d126039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108887, d126039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108888 q = 1) (hb : d125748 q = 1) : d126040 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108888, d126040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108888, d126040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d108889 q = 1) (hb : d125748 q = 1) : d126041 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108889, d126041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108889, d126041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro27356 (p : Pattern) (ha : d108895 p = 1) (hb : d125748 p = 1) : d126047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108890 q = 1) (hb : d125748 q = 1) : d126042 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108890, d126042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108890, d126042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27355 q ha hb
  have h2 (q : Pattern) (ha : d108891 q = 1) (hb : d125748 q = 1) : d126043 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108891, d126043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108891, d126043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108892 q = 1) (hb : d125748 q = 1) : d126044 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108892, d126044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108892, d126044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108893 q = 1) (hb : d125748 q = 1) : d126045 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108893, d126045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108893, d126045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108894 q = 1) (hb : d125748 q = 1) : d126046 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108894, d126046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108894, d126046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108895 q = 1) (hb : d125748 q = 1) : d126047 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108895, d126047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108895, d126047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27357 (p : Pattern) (ha : d11105 p = 1) (hb : d125748 p = 1) : d126051 p = 1 := by
  have h0 (q : Pattern) (ha : d11098 q = 1) (hb : d85721 q = 1) : d11098 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11101 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11102 q = 1) (hb : d125746 q = 1) : d126049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d125746, d126049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11102, d125746, d126049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11099 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12488 q ha hb
    | true =>
      simp only [d11099, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11100 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11100, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11101 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11101, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11103 q = 1) (hb : d125747 q = 1) : d88492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d125747, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11103, d125747, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11104 q = 1) (hb : d125748 q = 1) : d126050 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11104, d125748, d126050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11104, d125748, d126050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11105 q = 1) (hb : d125748 q = 1) : d126051 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11105, d126051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11105, d126051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27358 (p : Pattern) (ha : d11115 p = 1) (hb : d125748 p = 1) : d126057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27357 q ha hb
    | true =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11113 q = 1) (hb : d125748 q = 1) : d126055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11113, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11114 q = 1) (hb : d125748 q = 1) : d126056 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11114, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11115 q = 1) (hb : d125748 q = 1) : d126057 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11115, d126057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11115, d126057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27359 (p : Pattern) (ha : d11125 p = 1) (hb : d125748 p = 1) : d126063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11119 q = 1) (hb : d125748 q = 1) : d11119 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11120 q = 1) (hb : d125748 q = 1) : d126058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27358 q ha hb
    | true =>
      simp only [d11120, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11121 q = 1) (hb : d125748 q = 1) : d126059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11122 q = 1) (hb : d125748 q = 1) : d126060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11122, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11123 q = 1) (hb : d125748 q = 1) : d126061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11124 q = 1) (hb : d125748 q = 1) : d126062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11125 q = 1) (hb : d125748 q = 1) : d126063 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d126063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11125, d126063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27360 (p : Pattern) (ha : d11128 p = 1) (hb : d125748 p = 1) : d126066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27357 q ha hb
    | true =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11113 q = 1) (hb : d125748 q = 1) : d126055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11113, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11114 q = 1) (hb : d125748 q = 1) : d126056 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11114, d126056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11128 q = 1) (hb : d125748 q = 1) : d126066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11128, d126066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11128, d126066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27361 (p : Pattern) (ha : d11135 p = 1) (hb : d125748 p = 1) : d126072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11119 q = 1) (hb : d125748 q = 1) : d11119 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11120 q = 1) (hb : d125748 q = 1) : d126058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27358 q ha hb
    | true =>
      simp only [d11120, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11121 q = 1) (hb : d125748 q = 1) : d126059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11122 q = 1) (hb : d125748 q = 1) : d126060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11122, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11123 q = 1) (hb : d125748 q = 1) : d126061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11124 q = 1) (hb : d125748 q = 1) : d126062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11129 q = 1) (hb : d125748 q = 1) : d11129 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11130 q = 1) (hb : d125748 q = 1) : d126067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d126067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27360 q ha hb
    | true =>
      simp only [d11130, d126067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11131 q = 1) (hb : d125748 q = 1) : d126068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d126068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11132 q = 1) (hb : d125748 q = 1) : d126069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11132, d126069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11133 q = 1) (hb : d125748 q = 1) : d126070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d126070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11134 q = 1) (hb : d125748 q = 1) : d126071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d126071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11135 q = 1) (hb : d125748 q = 1) : d126072 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d126072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11135, d126072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro27362 (p : Pattern) (ha : d11243 p = 1) (hb : d125748 p = 1) : d126130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11119 q = 1) (hb : d125748 q = 1) : d11119 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11120 q = 1) (hb : d125748 q = 1) : d126058 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27358 q ha hb
    | true =>
      simp only [d11120, d126058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11121 q = 1) (hb : d125748 q = 1) : d126059 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d126059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11122 q = 1) (hb : d125748 q = 1) : d126060 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11122, d126060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11123 q = 1) (hb : d125748 q = 1) : d126061 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d126061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11124 q = 1) (hb : d125748 q = 1) : d126062 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d126062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11242 q = 1) (hb : d125748 q = 1) : d11242 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11243 q = 1) (hb : d125748 q = 1) : d126130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11243, d126130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11243, d126130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27363 (p : Pattern) (ha : d11140 p = 1) (hb : d125748 p = 1) : d126077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27357 q ha hb
    | true =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11113 q = 1) (hb : d125748 q = 1) : d126055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11113, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11139 q = 1) (hb : d125748 q = 1) : d126076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d126076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d126076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11140 q = 1) (hb : d125748 q = 1) : d126077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11140, d126077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11140, d126077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27364 (p : Pattern) (ha : d11149 p = 1) (hb : d125748 p = 1) : d126084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27357 q ha hb
    | true =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11147 q = 1) (hb : d125748 q = 1) : d126082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d126082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d126082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11148 q = 1) (hb : d125748 q = 1) : d126083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d126083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11148, d126083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11149 q = 1) (hb : d125748 q = 1) : d126084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11149, d126084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11149, d126084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27365 (p : Pattern) (ha : d11161 p = 1) (hb : d125748 p = 1) : d126091 p = 1 := by
  have h0 (q : Pattern) (ha : d11158 q = 1) (hb : d85721 q = 1) : d11158 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11159 q = 1) (hb : d125746 q = 1) : d126088 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11159, d125746, d126088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11159, d125746, d126088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11096 q = 1) (hb : d112686 q = 1) : d114443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12510 q ha hb
    | true =>
      simp only [d11096, d112686, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11097 q = 1) (hb : d112686 q = 1) : d114444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11097, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11098 q = 1) (hb : d112686 q = 1) : d114445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11098, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11101 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d11102 q = 1) (hb : d125747 q = 1) : d126089 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d125747, d126089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11102, d125747, d126089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d11160 q = 1) (hb : d125748 q = 1) : d126090 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11160, d125748, d126090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11160, d125748, d126090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11161 q = 1) (hb : d125748 q = 1) : d126091 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11161, d126091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11161, d126091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27366 (p : Pattern) (ha : d11167 p = 1) (hb : d125748 p = 1) : d126097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d125748 q = 1) : d126092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d126092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27365 q ha hb
    | true =>
      simp only [d11162, d126092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d125748 q = 1) : d126093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d126093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d126093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27357 q ha hb
    | true =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d125748 q = 1) : d126094 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d126094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d126094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d125748 q = 1) : d126095 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d126095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d126095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d125748 q = 1) : d126096 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d126096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d126096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11167 q = 1) (hb : d125748 q = 1) : d126097 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11167, d126097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11167, d126097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27367 (p : Pattern) (ha : d11200 p = 1) (hb : d125748 p = 1) : d126051 p = 1 := by
  have h0 (q : Pattern) (ha : d11098 q = 1) (hb : d85721 q = 1) : d11098 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11101 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11102 q = 1) (hb : d125746 q = 1) : d126049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d125746, d126049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11102, d125746, d126049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11195 q = 1) (hb : d112686 q = 1) : d88489 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11195, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25833 q ha hb
    | true =>
      simp only [d11195, d112686, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11196 q = 1) (hb : d112686 q = 1) : d88490 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11196, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11196, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11197 q = 1) (hb : d112686 q = 1) : d88491 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11197, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11197, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11198 q = 1) (hb : d125747 q = 1) : d88492 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11198, d125747, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11198, d125747, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11199 q = 1) (hb : d125748 q = 1) : d126050 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11199, d125748, d126050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11199, d125748, d126050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11200 q = 1) (hb : d125748 q = 1) : d126051 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11200, d126051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11200, d126051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27368 (p : Pattern) (ha : d11206 p = 1) (hb : d125748 p = 1) : d126103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27367 q ha hb
    | true =>
      simp only [d11201, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d125748 q = 1) : d126100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d126100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d126100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d125748 q = 1) : d126101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d126101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d126101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d125748 q = 1) : d126102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d126102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d126102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11206 q = 1) (hb : d125748 q = 1) : d126103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11206, d126103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11206, d126103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27369 (p : Pattern) (ha : d108901 p = 1) (hb : d125748 p = 1) : d126109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11142 q = 1) (hb : d125748 q = 1) : d11142 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11143 q = 1) (hb : d125748 q = 1) : d126078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d126078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27363 q ha hb
    | true =>
      simp only [d11143, d126078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11144 q = 1) (hb : d125748 q = 1) : d126079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d126079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d126079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11145 q = 1) (hb : d125748 q = 1) : d126080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d126080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11145, d126080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11146 q = 1) (hb : d125748 q = 1) : d126081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d126081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d126081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11152 q = 1) (hb : d125748 q = 1) : d11152 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11153 q = 1) (hb : d125748 q = 1) : d126085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d126085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27364 q ha hb
    | true =>
      simp only [d11153, d126085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11154 q = 1) (hb : d125748 q = 1) : d126086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d126086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d126086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11155 q = 1) (hb : d125748 q = 1) : d126087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d126087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11155, d126087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11168 q = 1) (hb : d125748 q = 1) : d126098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d126098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27366 q ha hb
    | true =>
      simp only [d11168, d126098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27358 q ha hb
  have h11 (q : Pattern) (ha : d108897 q = 1) (hb : d125748 q = 1) : d126099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d126099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108897, d126099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11207 q = 1) (hb : d125748 q = 1) : d126104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d126104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27368 q ha hb
    | true =>
      simp only [d11207, d126104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11208 q = 1) (hb : d125748 q = 1) : d126105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d126105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11208, d126105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108898 q = 1) (hb : d125748 q = 1) : d126106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d126106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108898, d126106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108899 q = 1) (hb : d125748 q = 1) : d126107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d126107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108899, d126107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108900 q = 1) (hb : d125748 q = 1) : d126108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d126108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108900, d126108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108901 q = 1) (hb : d125748 q = 1) : d126109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108901, d126109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108901, d126109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro27370 (p : Pattern) (ha : d11213 p = 1) (hb : d125748 p = 1) : d126110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27357 q ha hb
    | true =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11113 q = 1) (hb : d125748 q = 1) : d126055 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11113, d126055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11139 q = 1) (hb : d125748 q = 1) : d126076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d126076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d126076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11213 q = 1) (hb : d125748 q = 1) : d126110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11213, d126110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11213, d126110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27371 (p : Pattern) (ha : d11219 p = 1) (hb : d125748 p = 1) : d126115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27357 q ha hb
    | true =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11111 q = 1) (hb : d125748 q = 1) : d11111 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11112 q = 1) (hb : d125748 q = 1) : d126054 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d126054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11147 q = 1) (hb : d125748 q = 1) : d126082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d126082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d126082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11148 q = 1) (hb : d125748 q = 1) : d126083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d126083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11148, d126083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11219 q = 1) (hb : d125748 q = 1) : d126115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11219, d126115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11219, d126115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27372 (p : Pattern) (ha : d11224 p = 1) (hb : d125748 p = 1) : d126119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d125748 q = 1) : d126092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d126092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27365 q ha hb
    | true =>
      simp only [d11162, d126092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d125748 q = 1) : d126093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d126093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d126093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27357 q ha hb
    | true =>
      simp only [d11106, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d125748 q = 1) : d126094 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d126094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d126094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d125748 q = 1) : d126095 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d126095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d126095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d125748 q = 1) : d126096 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d126096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d126096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11224 q = 1) (hb : d125748 q = 1) : d126119 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11224, d126119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11224, d126119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27373 (p : Pattern) (ha : d11230 p = 1) (hb : d125748 p = 1) : d126122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d125748 q = 1) : d126052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27367 q ha hb
    | true =>
      simp only [d11201, d126052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d125748 q = 1) : d126053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d126053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d125748 q = 1) : d126100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d126100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d126100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d125748 q = 1) : d126101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d126101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d126101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d125748 q = 1) : d126102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d126102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d126102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11230 q = 1) (hb : d125748 q = 1) : d126122 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11230, d126122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11230, d126122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27374 (p : Pattern) (ha : d108906 p = 1) (hb : d125748 p = 1) : d126128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11142 q = 1) (hb : d125748 q = 1) : d11142 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11143 q = 1) (hb : d125748 q = 1) : d126078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d126078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27363 q ha hb
    | true =>
      simp only [d11143, d126078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11144 q = 1) (hb : d125748 q = 1) : d126079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d126079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d126079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11145 q = 1) (hb : d125748 q = 1) : d126080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d126080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11145, d126080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11146 q = 1) (hb : d125748 q = 1) : d126081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d126081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d126081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11152 q = 1) (hb : d125748 q = 1) : d11152 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11153 q = 1) (hb : d125748 q = 1) : d126085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d126085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27364 q ha hb
    | true =>
      simp only [d11153, d126085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11154 q = 1) (hb : d125748 q = 1) : d126086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d126086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d126086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11155 q = 1) (hb : d125748 q = 1) : d126087 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d126087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11155, d126087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11168 q = 1) (hb : d125748 q = 1) : d126098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d126098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27366 q ha hb
    | true =>
      simp only [d11168, d126098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27358 q ha hb
  have h11 (q : Pattern) (ha : d108897 q = 1) (hb : d125748 q = 1) : d126099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108897, d126099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108897, d126099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11207 q = 1) (hb : d125748 q = 1) : d126104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d126104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27368 q ha hb
    | true =>
      simp only [d11207, d126104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11208 q = 1) (hb : d125748 q = 1) : d126105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d126105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11208, d126105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108898 q = 1) (hb : d125748 q = 1) : d126106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108898, d126106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108898, d126106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108899 q = 1) (hb : d125748 q = 1) : d126107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108899, d126107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108899, d126107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108900 q = 1) (hb : d125748 q = 1) : d126108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108900, d126108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108900, d126108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11214 q = 1) (hb : d125748 q = 1) : d11214 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d11215 q = 1) (hb : d125748 q = 1) : d126111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11215, d126111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27370 q ha hb
    | true =>
      simp only [d11215, d126111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11216 q = 1) (hb : d125748 q = 1) : d126112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11216, d126112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11216, d126112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d11217 q = 1) (hb : d125748 q = 1) : d126113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11217, d126113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d11217, d126113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d11218 q = 1) (hb : d125748 q = 1) : d126114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11218, d126114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11218, d126114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d11220 q = 1) (hb : d125748 q = 1) : d11220 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d11221 q = 1) (hb : d125748 q = 1) : d126116 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11221, d126116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27371 q ha hb
    | true =>
      simp only [d11221, d126116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d11222 q = 1) (hb : d125748 q = 1) : d126117 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11222, d126117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11222, d126117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d11223 q = 1) (hb : d125748 q = 1) : d126118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11223, d126118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11223, d126118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d11225 q = 1) (hb : d125748 q = 1) : d126120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d126120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27372 q ha hb
    | true =>
      simp only [d11225, d126120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27360 q ha hb
  have h27 (q : Pattern) (ha : d108902 q = 1) (hb : d125748 q = 1) : d126121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d126121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108902, d126121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d11231 q = 1) (hb : d125748 q = 1) : d126123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d126123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27373 q ha hb
    | true =>
      simp only [d11231, d126123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d11232 q = 1) (hb : d125748 q = 1) : d126124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d126124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d11232, d126124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d108903 q = 1) (hb : d125748 q = 1) : d126125 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d126125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108903, d126125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108904 q = 1) (hb : d125748 q = 1) : d126126 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108904, d126126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108904, d126126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d108905 q = 1) (hb : d125748 q = 1) : d126127 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108905, d126127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108905, d126127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d108906 q = 1) (hb : d125748 q = 1) : d126128 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108906, d126128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108906, d126128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro27375 (p : Pattern) (ha : d108913 p = 1) (hb : d125748 p = 1) : d126137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11225 q = 1) (hb : d125748 q = 1) : d126120 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d126120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27372 q ha hb
    | true =>
      simp only [d11225, d126120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27360 q ha hb
  have h2 (q : Pattern) (ha : d108902 q = 1) (hb : d125748 q = 1) : d126121 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108902, d126121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108902, d126121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11231 q = 1) (hb : d125748 q = 1) : d126123 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d126123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27373 q ha hb
    | true =>
      simp only [d11231, d126123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11232 q = 1) (hb : d125748 q = 1) : d126124 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d126124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11232, d126124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108903 q = 1) (hb : d125748 q = 1) : d126125 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108903, d126125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108903, d126125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108911 q = 1) (hb : d125748 q = 1) : d126135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108911, d126135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108911, d126135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108912 q = 1) (hb : d125748 q = 1) : d126136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108912, d126136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108912, d126136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108913 q = 1) (hb : d125748 q = 1) : d126137 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108913, d126137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108913, d126137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27376 (p : Pattern) (ha : d11276 p = 1) (hb : d125748 p = 1) : d126146 p = 1 := by
  have h0 (q : Pattern) (ha : d11266 q = 1) (hb : d85721 q = 1) : d11266 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11270 q = 1) (hb : d125746 q = 1) : d126143 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11270, d125746, d126143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11270, d125746, d126143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11267 q = 1) (hb : d112686 q = 1) : d114500 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12527 q ha hb
    | true =>
      simp only [d11267, d112686, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11268 q = 1) (hb : d112686 q = 1) : d114501 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11268, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11269 q = 1) (hb : d112686 q = 1) : d114502 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11269, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11273 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d11274 q = 1) (hb : d125747 q = 1) : d126144 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d125747, d126144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11274, d125747, d126144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d11275 q = 1) (hb : d125748 q = 1) : d126145 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11275, d125748, d126145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11275, d125748, d126145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11276 q = 1) (hb : d125748 q = 1) : d126146 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11276, d126146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11276, d126146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27377 (p : Pattern) (ha : d11281 p = 1) (hb : d125748 p = 1) : d126151 p = 1 := by
  have h0 (q : Pattern) (ha : d11269 q = 1) (hb : d85721 q = 1) : d11269 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11273 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11274 q = 1) (hb : d125746 q = 1) : d126149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d125746, d126149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11274, d125746, d126149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11271 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12524 q ha hb
    | true =>
      simp only [d11271, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11272 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11272, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11273 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11273, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11279 q = 1) (hb : d125747 q = 1) : d88556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d125747, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11279, d125747, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11280 q = 1) (hb : d125748 q = 1) : d126150 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11280, d125748, d126150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11280, d125748, d126150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11281 q = 1) (hb : d125748 q = 1) : d126151 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11281, d126151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11281, d126151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27378 (p : Pattern) (ha : d11287 p = 1) (hb : d125748 p = 1) : d126157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11277 q = 1) (hb : d125748 q = 1) : d126147 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11277, d126147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27376 q ha hb
    | true =>
      simp only [d11277, d126147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11278 q = 1) (hb : d125748 q = 1) : d126148 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11278, d126148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11278, d126148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11282 q = 1) (hb : d125748 q = 1) : d126152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27377 q ha hb
    | true =>
      simp only [d11282, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11283 q = 1) (hb : d125748 q = 1) : d126153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11284 q = 1) (hb : d125748 q = 1) : d126154 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11284, d126154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11284, d126154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11285 q = 1) (hb : d125748 q = 1) : d126155 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11285, d126155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11285, d126155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11286 q = 1) (hb : d125748 q = 1) : d126156 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11286, d126156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11286, d126156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11287 q = 1) (hb : d125748 q = 1) : d126157 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11287, d126157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11287, d126157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27379 (p : Pattern) (ha : d11295 p = 1) (hb : d125748 p = 1) : d126161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11282 q = 1) (hb : d125748 q = 1) : d126152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27377 q ha hb
    | true =>
      simp only [d11282, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11283 q = 1) (hb : d125748 q = 1) : d126153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11283, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11291 q = 1) (hb : d125748 q = 1) : d11291 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11292 q = 1) (hb : d125748 q = 1) : d126158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11292, d126158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11292, d126158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11293 q = 1) (hb : d125748 q = 1) : d126159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11293, d126159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11293, d126159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11294 q = 1) (hb : d125748 q = 1) : d126160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11294, d126160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11294, d126160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11295 q = 1) (hb : d125748 q = 1) : d126161 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11295, d126161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11295, d126161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27380 (p : Pattern) (ha : d11328 p = 1) (hb : d125748 p = 1) : d126151 p = 1 := by
  have h0 (q : Pattern) (ha : d11269 q = 1) (hb : d85721 q = 1) : d11269 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11273 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11274 q = 1) (hb : d125746 q = 1) : d126149 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d125746, d126149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11274, d125746, d126149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11323 q = 1) (hb : d112686 q = 1) : d88553 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11323, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25849 q ha hb
    | true =>
      simp only [d11323, d112686, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11324 q = 1) (hb : d112686 q = 1) : d88554 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11324, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11324, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11325 q = 1) (hb : d112686 q = 1) : d88555 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11325, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11325, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11326 q = 1) (hb : d125747 q = 1) : d88556 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11326, d125747, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11326, d125747, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11327 q = 1) (hb : d125748 q = 1) : d126150 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11327, d125748, d126150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11327, d125748, d126150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11328 q = 1) (hb : d125748 q = 1) : d126151 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11328, d126151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11328, d126151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27381 (p : Pattern) (ha : d11334 p = 1) (hb : d125748 p = 1) : d126167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11329 q = 1) (hb : d125748 q = 1) : d126152 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11329, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27380 q ha hb
    | true =>
      simp only [d11329, d126152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11330 q = 1) (hb : d125748 q = 1) : d126153 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11330, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11330, d126153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11331 q = 1) (hb : d125748 q = 1) : d126164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11331, d126164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11331, d126164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11332 q = 1) (hb : d125748 q = 1) : d126165 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11332, d126165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11332, d126165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11333 q = 1) (hb : d125748 q = 1) : d126166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11333, d126166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11333, d126166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11334 q = 1) (hb : d125748 q = 1) : d126167 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11334, d126167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11334, d126167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27382 (p : Pattern) (ha : d108923 p = 1) (hb : d125748 p = 1) : d126173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11296 q = 1) (hb : d125748 q = 1) : d126162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11296, d126162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27378 q ha hb
    | true =>
      simp only [d11296, d126162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27379 q ha hb
  have h2 (q : Pattern) (ha : d108919 q = 1) (hb : d125748 q = 1) : d126163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108919, d126163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108919, d126163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11335 q = 1) (hb : d125748 q = 1) : d126168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11335, d126168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27381 q ha hb
    | true =>
      simp only [d11335, d126168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11336 q = 1) (hb : d125748 q = 1) : d126169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11336, d126169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11336, d126169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108920 q = 1) (hb : d125748 q = 1) : d126170 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108920, d126170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108920, d126170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108921 q = 1) (hb : d125748 q = 1) : d126171 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108921, d126171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108921, d126171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108922 q = 1) (hb : d125748 q = 1) : d126172 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108922, d126172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108922, d126172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108923 q = 1) (hb : d125748 q = 1) : d126173 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108923, d126173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108923, d126173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27383 (p : Pattern) (ha : d108929 p = 1) (hb : d125748 p = 1) : d126179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11126 q = 1) (hb : d125748 q = 1) : d126064 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11126, d126064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11126, d126064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27359 q ha hb
  have h2 (q : Pattern) (ha : d11127 q = 1) (hb : d125748 q = 1) : d126065 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11127, d126065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11127, d126065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11136 q = 1) (hb : d125748 q = 1) : d126073 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27359 q ha hb
    | true =>
      simp only [d11136, d126073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27361 q ha hb
  have h4 (q : Pattern) (ha : d11137 q = 1) (hb : d125748 q = 1) : d126074 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11137, d126074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11138 q = 1) (hb : d125748 q = 1) : d126075 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11138, d126075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11138, d126075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108907 q = 1) (hb : d125748 q = 1) : d126129 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108907, d126129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27369 q ha hb
    | true =>
      simp only [d108907, d126129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27374 q ha hb
  have h7 (q : Pattern) (ha : d11249 q = 1) (hb : d125748 q = 1) : d11249 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11250 q = 1) (hb : d125748 q = 1) : d126131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11250, d126131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27362 q ha hb
    | true =>
      simp only [d11250, d126131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108908 q = 1) (hb : d125748 q = 1) : d126132 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108908, d126132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108908, d126132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108909 q = 1) (hb : d125748 q = 1) : d126133 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108909, d126133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108909, d126133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d108910 q = 1) (hb : d125748 q = 1) : d126134 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108910, d126134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108910, d126134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108914 q = 1) (hb : d125748 q = 1) : d126138 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108914, d126138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108914, d126138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27375 q ha hb
  have h13 (q : Pattern) (ha : d11259 q = 1) (hb : d125748 q = 1) : d11259 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d108915 q = 1) (hb : d125748 q = 1) : d126139 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108915, d126139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108915, d126139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108916 q = 1) (hb : d125748 q = 1) : d126140 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108916, d126140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108916, d126140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108917 q = 1) (hb : d125748 q = 1) : d126141 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108917, d126141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108917, d126141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d108918 q = 1) (hb : d125748 q = 1) : d126142 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108918, d126142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108918, d126142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108924 q = 1) (hb : d125748 q = 1) : d126174 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108924, d126174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108924, d126174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27382 q ha hb
  have h19 (q : Pattern) (ha : d11352 q = 1) (hb : d125748 q = 1) : d11352 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d108925 q = 1) (hb : d125748 q = 1) : d126175 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108925, d126175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108925, d126175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d108926 q = 1) (hb : d125748 q = 1) : d126176 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108926, d126176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108926, d126176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108927 q = 1) (hb : d125748 q = 1) : d126177 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108927, d126177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108927, d126177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108928 q = 1) (hb : d125748 q = 1) : d126178 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108928, d126178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108928, d126178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d108929 q = 1) (hb : d125748 q = 1) : d126179 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108929, d126179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108929, d126179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro27384 (p : Pattern) (ha : d108935 p = 1) (hb : d125748 p = 1) : d126185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108930 q = 1) (hb : d125748 q = 1) : d126180 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108930, d126180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108930, d126180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27383 q ha hb
  have h2 (q : Pattern) (ha : d108931 q = 1) (hb : d125748 q = 1) : d126181 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108931, d126181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108931, d126181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108932 q = 1) (hb : d125748 q = 1) : d126182 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108932, d126182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108932, d126182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108933 q = 1) (hb : d125748 q = 1) : d126183 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108933, d126183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108933, d126183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108934 q = 1) (hb : d125748 q = 1) : d126184 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108934, d126184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108934, d126184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108935 q = 1) (hb : d125748 q = 1) : d126185 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108935, d126185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108935, d126185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27385 (p : Pattern) (ha : d11375 p = 1) (hb : d125748 p = 1) : d126190 p = 1 := by
  have h0 (q : Pattern) (ha : d11368 q = 1) (hb : d85721 q = 1) : d11368 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11371 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11372 q = 1) (hb : d125746 q = 1) : d126188 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d125746, d126188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11372, d125746, d126188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11369 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12536 q ha hb
    | true =>
      simp only [d11369, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11370 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11370, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11371 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11371, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11373 q = 1) (hb : d125747 q = 1) : d88644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d125747, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11373, d125747, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11374 q = 1) (hb : d125748 q = 1) : d126189 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11374, d125748, d126189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11374, d125748, d126189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11375 q = 1) (hb : d125748 q = 1) : d126190 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11375, d126190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11375, d126190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27386 (p : Pattern) (ha : d11385 p = 1) (hb : d125748 p = 1) : d126196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27385 q ha hb
    | true =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11383 q = 1) (hb : d125748 q = 1) : d126194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11383, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11384 q = 1) (hb : d125748 q = 1) : d126195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11384, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11385 q = 1) (hb : d125748 q = 1) : d126196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11385, d126196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11385, d126196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27387 (p : Pattern) (ha : d11395 p = 1) (hb : d125748 p = 1) : d126202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11389 q = 1) (hb : d125748 q = 1) : d11389 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11390 q = 1) (hb : d125748 q = 1) : d126197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27386 q ha hb
    | true =>
      simp only [d11390, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11391 q = 1) (hb : d125748 q = 1) : d126198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11392 q = 1) (hb : d125748 q = 1) : d126199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11392, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11393 q = 1) (hb : d125748 q = 1) : d126200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11394 q = 1) (hb : d125748 q = 1) : d126201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11395 q = 1) (hb : d125748 q = 1) : d126202 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11395, d126202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11395, d126202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27388 (p : Pattern) (ha : d11398 p = 1) (hb : d125748 p = 1) : d126205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27385 q ha hb
    | true =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11383 q = 1) (hb : d125748 q = 1) : d126194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11383, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11384 q = 1) (hb : d125748 q = 1) : d126195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11384, d126195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11398 q = 1) (hb : d125748 q = 1) : d126205 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11398, d126205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11398, d126205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27389 (p : Pattern) (ha : d11405 p = 1) (hb : d125748 p = 1) : d126211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11389 q = 1) (hb : d125748 q = 1) : d11389 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11390 q = 1) (hb : d125748 q = 1) : d126197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27386 q ha hb
    | true =>
      simp only [d11390, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11391 q = 1) (hb : d125748 q = 1) : d126198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11392 q = 1) (hb : d125748 q = 1) : d126199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11392, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11393 q = 1) (hb : d125748 q = 1) : d126200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11394 q = 1) (hb : d125748 q = 1) : d126201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11399 q = 1) (hb : d125748 q = 1) : d11399 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11400 q = 1) (hb : d125748 q = 1) : d126206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d126206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27388 q ha hb
    | true =>
      simp only [d11400, d126206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11401 q = 1) (hb : d125748 q = 1) : d126207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d126207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11402 q = 1) (hb : d125748 q = 1) : d126208 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11402, d126208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11403 q = 1) (hb : d125748 q = 1) : d126209 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d126209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11404 q = 1) (hb : d125748 q = 1) : d126210 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d126210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11405 q = 1) (hb : d125748 q = 1) : d126211 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11405, d126211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11405, d126211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro27390 (p : Pattern) (ha : d11513 p = 1) (hb : d125748 p = 1) : d126269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11389 q = 1) (hb : d125748 q = 1) : d11389 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11390 q = 1) (hb : d125748 q = 1) : d126197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27386 q ha hb
    | true =>
      simp only [d11390, d126197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11391 q = 1) (hb : d125748 q = 1) : d126198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11391, d126198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11392 q = 1) (hb : d125748 q = 1) : d126199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11392, d126199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11393 q = 1) (hb : d125748 q = 1) : d126200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11393, d126200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11394 q = 1) (hb : d125748 q = 1) : d126201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11394, d126201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11512 q = 1) (hb : d125748 q = 1) : d11512 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11513 q = 1) (hb : d125748 q = 1) : d126269 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11513, d126269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11513, d126269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27391 (p : Pattern) (ha : d11410 p = 1) (hb : d125748 p = 1) : d126216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27385 q ha hb
    | true =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11383 q = 1) (hb : d125748 q = 1) : d126194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11383, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11409 q = 1) (hb : d125748 q = 1) : d126215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d126215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d126215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11410 q = 1) (hb : d125748 q = 1) : d126216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11410, d126216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11410, d126216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27392 (p : Pattern) (ha : d11419 p = 1) (hb : d125748 p = 1) : d126223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27385 q ha hb
    | true =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11417 q = 1) (hb : d125748 q = 1) : d126221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d126221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d126221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11418 q = 1) (hb : d125748 q = 1) : d126222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d126222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11418, d126222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11419 q = 1) (hb : d125748 q = 1) : d126223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11419, d126223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11419, d126223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27393 (p : Pattern) (ha : d11431 p = 1) (hb : d125748 p = 1) : d126230 p = 1 := by
  have h0 (q : Pattern) (ha : d11428 q = 1) (hb : d85721 q = 1) : d11428 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11368 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11429 q = 1) (hb : d125746 q = 1) : d126227 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11429, d125746, d126227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11429, d125746, d126227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11366 q = 1) (hb : d112686 q = 1) : d114586 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12559 q ha hb
    | true =>
      simp only [d11366, d112686, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11367 q = 1) (hb : d112686 q = 1) : d114587 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11367, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11368 q = 1) (hb : d112686 q = 1) : d114588 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11368, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d11372 q = 1) (hb : d125747 q = 1) : d126228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d125747, d126228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11372, d125747, d126228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d11430 q = 1) (hb : d125748 q = 1) : d126229 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11430, d125748, d126229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11430, d125748, d126229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11431 q = 1) (hb : d125748 q = 1) : d126230 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11431, d126230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11431, d126230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27394 (p : Pattern) (ha : d11437 p = 1) (hb : d125748 p = 1) : d126236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d125748 q = 1) : d126231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d126231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27393 q ha hb
    | true =>
      simp only [d11432, d126231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d125748 q = 1) : d126232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d126232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d126232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27385 q ha hb
    | true =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d125748 q = 1) : d126233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d126233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d126233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d125748 q = 1) : d126234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d126234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d126234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d125748 q = 1) : d126235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d126235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d126235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11437 q = 1) (hb : d125748 q = 1) : d126236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11437, d126236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11437, d126236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27395 (p : Pattern) (ha : d11470 p = 1) (hb : d125748 p = 1) : d126190 p = 1 := by
  have h0 (q : Pattern) (ha : d11368 q = 1) (hb : d85721 q = 1) : d11368 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11371 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11372 q = 1) (hb : d125746 q = 1) : d126188 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d125746, d126188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11372, d125746, d126188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11465 q = 1) (hb : d112686 q = 1) : d88641 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11465, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25875 q ha hb
    | true =>
      simp only [d11465, d112686, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11466 q = 1) (hb : d112686 q = 1) : d88642 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11466, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11466, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11467 q = 1) (hb : d112686 q = 1) : d88643 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11467, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11467, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11468 q = 1) (hb : d125747 q = 1) : d88644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11468, d125747, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11468, d125747, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11469 q = 1) (hb : d125748 q = 1) : d126189 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11469, d125748, d126189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11469, d125748, d126189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11470 q = 1) (hb : d125748 q = 1) : d126190 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11470, d126190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11470, d126190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27396 (p : Pattern) (ha : d11476 p = 1) (hb : d125748 p = 1) : d126242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27395 q ha hb
    | true =>
      simp only [d11471, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d125748 q = 1) : d126239 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d126239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d126239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d125748 q = 1) : d126240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d126240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d126240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d125748 q = 1) : d126241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d126241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d126241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11476 q = 1) (hb : d125748 q = 1) : d126242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11476, d126242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11476, d126242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27397 (p : Pattern) (ha : d108942 p = 1) (hb : d125748 p = 1) : d126248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11412 q = 1) (hb : d125748 q = 1) : d11412 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11413 q = 1) (hb : d125748 q = 1) : d126217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d126217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27391 q ha hb
    | true =>
      simp only [d11413, d126217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11414 q = 1) (hb : d125748 q = 1) : d126218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d126218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d126218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11415 q = 1) (hb : d125748 q = 1) : d126219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d126219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11415, d126219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11416 q = 1) (hb : d125748 q = 1) : d126220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d126220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d126220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11422 q = 1) (hb : d125748 q = 1) : d11422 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11423 q = 1) (hb : d125748 q = 1) : d126224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d126224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27392 q ha hb
    | true =>
      simp only [d11423, d126224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11424 q = 1) (hb : d125748 q = 1) : d126225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d126225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d126225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11425 q = 1) (hb : d125748 q = 1) : d126226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d126226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11425, d126226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11438 q = 1) (hb : d125748 q = 1) : d126237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d126237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27394 q ha hb
    | true =>
      simp only [d11438, d126237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27386 q ha hb
  have h11 (q : Pattern) (ha : d108938 q = 1) (hb : d125748 q = 1) : d126238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d126238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108938, d126238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11477 q = 1) (hb : d125748 q = 1) : d126243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d126243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27396 q ha hb
    | true =>
      simp only [d11477, d126243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11478 q = 1) (hb : d125748 q = 1) : d126244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d126244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11478, d126244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108939 q = 1) (hb : d125748 q = 1) : d126245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d126245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108939, d126245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108940 q = 1) (hb : d125748 q = 1) : d126246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d126246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108940, d126246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108941 q = 1) (hb : d125748 q = 1) : d126247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d126247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108941, d126247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108942 q = 1) (hb : d125748 q = 1) : d126248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108942, d126248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108942, d126248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro27398 (p : Pattern) (ha : d11483 p = 1) (hb : d125748 p = 1) : d126249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27385 q ha hb
    | true =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11383 q = 1) (hb : d125748 q = 1) : d126194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11383, d126194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11409 q = 1) (hb : d125748 q = 1) : d126215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d126215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11409, d126215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11483 q = 1) (hb : d125748 q = 1) : d126249 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11483, d126249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11483, d126249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27399 (p : Pattern) (ha : d11489 p = 1) (hb : d125748 p = 1) : d126254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11376 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27385 q ha hb
    | true =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11377 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11381 q = 1) (hb : d125748 q = 1) : d11381 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11382 q = 1) (hb : d125748 q = 1) : d126193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11382, d126193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11417 q = 1) (hb : d125748 q = 1) : d126221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d126221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11417, d126221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11418 q = 1) (hb : d125748 q = 1) : d126222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d126222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11418, d126222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11489 q = 1) (hb : d125748 q = 1) : d126254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11489, d126254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11489, d126254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27400 (p : Pattern) (ha : d11494 p = 1) (hb : d125748 p = 1) : d126258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11432 q = 1) (hb : d125748 q = 1) : d126231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d126231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27393 q ha hb
    | true =>
      simp only [d11432, d126231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11433 q = 1) (hb : d125748 q = 1) : d126232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d126232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11433, d126232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11376 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27385 q ha hb
    | true =>
      simp only [d11376, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11377 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11377, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11434 q = 1) (hb : d125748 q = 1) : d126233 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d126233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11434, d126233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11435 q = 1) (hb : d125748 q = 1) : d126234 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d126234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11435, d126234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11436 q = 1) (hb : d125748 q = 1) : d126235 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d126235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11436, d126235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11494 q = 1) (hb : d125748 q = 1) : d126258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11494, d126258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11494, d126258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27401 (p : Pattern) (ha : d11500 p = 1) (hb : d125748 p = 1) : d126261 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11471 q = 1) (hb : d125748 q = 1) : d126191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27395 q ha hb
    | true =>
      simp only [d11471, d126191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11472 q = 1) (hb : d125748 q = 1) : d126192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11472, d126192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11473 q = 1) (hb : d125748 q = 1) : d126239 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d126239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11473, d126239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11474 q = 1) (hb : d125748 q = 1) : d126240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d126240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11474, d126240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11475 q = 1) (hb : d125748 q = 1) : d126241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d126241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11475, d126241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11500 q = 1) (hb : d125748 q = 1) : d126261 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11500, d126261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11500, d126261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27402 (p : Pattern) (ha : d108947 p = 1) (hb : d125748 p = 1) : d126267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11412 q = 1) (hb : d125748 q = 1) : d11412 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11413 q = 1) (hb : d125748 q = 1) : d126217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d126217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27391 q ha hb
    | true =>
      simp only [d11413, d126217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11414 q = 1) (hb : d125748 q = 1) : d126218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d126218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11414, d126218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11415 q = 1) (hb : d125748 q = 1) : d126219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d126219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11415, d126219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11416 q = 1) (hb : d125748 q = 1) : d126220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d126220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11416, d126220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11422 q = 1) (hb : d125748 q = 1) : d11422 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11423 q = 1) (hb : d125748 q = 1) : d126224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d126224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27392 q ha hb
    | true =>
      simp only [d11423, d126224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11424 q = 1) (hb : d125748 q = 1) : d126225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d126225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11424, d126225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11425 q = 1) (hb : d125748 q = 1) : d126226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d126226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11425, d126226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11438 q = 1) (hb : d125748 q = 1) : d126237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d126237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27394 q ha hb
    | true =>
      simp only [d11438, d126237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27386 q ha hb
  have h11 (q : Pattern) (ha : d108938 q = 1) (hb : d125748 q = 1) : d126238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108938, d126238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108938, d126238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11477 q = 1) (hb : d125748 q = 1) : d126243 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d126243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27396 q ha hb
    | true =>
      simp only [d11477, d126243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11478 q = 1) (hb : d125748 q = 1) : d126244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d126244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11478, d126244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108939 q = 1) (hb : d125748 q = 1) : d126245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108939, d126245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108939, d126245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108940 q = 1) (hb : d125748 q = 1) : d126246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108940, d126246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108940, d126246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108941 q = 1) (hb : d125748 q = 1) : d126247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108941, d126247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108941, d126247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11484 q = 1) (hb : d125748 q = 1) : d11484 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d11485 q = 1) (hb : d125748 q = 1) : d126250 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11485, d126250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27398 q ha hb
    | true =>
      simp only [d11485, d126250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11486 q = 1) (hb : d125748 q = 1) : d126251 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11486, d126251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11486, d126251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d11487 q = 1) (hb : d125748 q = 1) : d126252 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11487, d126252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d11487, d126252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d11488 q = 1) (hb : d125748 q = 1) : d126253 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11488, d126253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11488, d126253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d11490 q = 1) (hb : d125748 q = 1) : d11490 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d11491 q = 1) (hb : d125748 q = 1) : d126255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11491, d126255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27399 q ha hb
    | true =>
      simp only [d11491, d126255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d11492 q = 1) (hb : d125748 q = 1) : d126256 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11492, d126256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11492, d126256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d11493 q = 1) (hb : d125748 q = 1) : d126257 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11493, d126257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11493, d126257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d11495 q = 1) (hb : d125748 q = 1) : d126259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d126259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27400 q ha hb
    | true =>
      simp only [d11495, d126259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27388 q ha hb
  have h27 (q : Pattern) (ha : d108943 q = 1) (hb : d125748 q = 1) : d126260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d126260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108943, d126260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d11501 q = 1) (hb : d125748 q = 1) : d126262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d126262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27401 q ha hb
    | true =>
      simp only [d11501, d126262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d11502 q = 1) (hb : d125748 q = 1) : d126263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d126263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d11502, d126263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d108944 q = 1) (hb : d125748 q = 1) : d126264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d126264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108944, d126264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108945 q = 1) (hb : d125748 q = 1) : d126265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108945, d126265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108945, d126265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d108946 q = 1) (hb : d125748 q = 1) : d126266 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108946, d126266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108946, d126266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d108947 q = 1) (hb : d125748 q = 1) : d126267 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108947, d126267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108947, d126267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro27403 (p : Pattern) (ha : d108954 p = 1) (hb : d125748 p = 1) : d126276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11495 q = 1) (hb : d125748 q = 1) : d126259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d126259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27400 q ha hb
    | true =>
      simp only [d11495, d126259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27388 q ha hb
  have h2 (q : Pattern) (ha : d108943 q = 1) (hb : d125748 q = 1) : d126260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108943, d126260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108943, d126260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11501 q = 1) (hb : d125748 q = 1) : d126262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d126262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27401 q ha hb
    | true =>
      simp only [d11501, d126262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11502 q = 1) (hb : d125748 q = 1) : d126263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d126263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11502, d126263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108944 q = 1) (hb : d125748 q = 1) : d126264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108944, d126264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108944, d126264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108952 q = 1) (hb : d125748 q = 1) : d126274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108952, d126274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108952, d126274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108953 q = 1) (hb : d125748 q = 1) : d126275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108953, d126275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108953, d126275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108954 q = 1) (hb : d125748 q = 1) : d126276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108954, d126276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108954, d126276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27404 (p : Pattern) (ha : d11546 p = 1) (hb : d125748 p = 1) : d126285 p = 1 := by
  have h0 (q : Pattern) (ha : d11536 q = 1) (hb : d85721 q = 1) : d11536 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11540 q = 1) (hb : d125746 q = 1) : d126282 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11540, d125746, d126282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11540, d125746, d126282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11537 q = 1) (hb : d112686 q = 1) : d114643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12577 q ha hb
    | true =>
      simp only [d11537, d112686, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11538 q = 1) (hb : d112686 q = 1) : d114644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11538, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11539 q = 1) (hb : d112686 q = 1) : d114645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11539, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11543 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d11544 q = 1) (hb : d125747 q = 1) : d126283 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d125747, d126283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11544, d125747, d126283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d11545 q = 1) (hb : d125748 q = 1) : d126284 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11545, d125748, d126284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11545, d125748, d126284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11546 q = 1) (hb : d125748 q = 1) : d126285 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11546, d126285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11546, d126285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27405 (p : Pattern) (ha : d11551 p = 1) (hb : d125748 p = 1) : d126290 p = 1 := by
  have h0 (q : Pattern) (ha : d11539 q = 1) (hb : d85721 q = 1) : d11539 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11544 q = 1) (hb : d125746 q = 1) : d126288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d125746, d126288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11544, d125746, d126288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11541 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12573 q ha hb
    | true =>
      simp only [d11541, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11542 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11542, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11543 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11543, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11549 q = 1) (hb : d125747 q = 1) : d88708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d125747, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11549, d125747, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11550 q = 1) (hb : d125748 q = 1) : d126289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11550, d125748, d126289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11550, d125748, d126289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11551 q = 1) (hb : d125748 q = 1) : d126290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11551, d126290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11551, d126290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27406 (p : Pattern) (ha : d11557 p = 1) (hb : d125748 p = 1) : d126296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11547 q = 1) (hb : d125748 q = 1) : d126286 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11547, d126286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27404 q ha hb
    | true =>
      simp only [d11547, d126286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11548 q = 1) (hb : d125748 q = 1) : d126287 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11548, d126287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11548, d126287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11552 q = 1) (hb : d125748 q = 1) : d126291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27405 q ha hb
    | true =>
      simp only [d11552, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11553 q = 1) (hb : d125748 q = 1) : d126292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11554 q = 1) (hb : d125748 q = 1) : d126293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11554, d126293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11554, d126293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11555 q = 1) (hb : d125748 q = 1) : d126294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11555, d126294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11555, d126294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11556 q = 1) (hb : d125748 q = 1) : d126295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11556, d126295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11556, d126295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11557 q = 1) (hb : d125748 q = 1) : d126296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11557, d126296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11557, d126296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27407 (p : Pattern) (ha : d11565 p = 1) (hb : d125748 p = 1) : d126300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11552 q = 1) (hb : d125748 q = 1) : d126291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27405 q ha hb
    | true =>
      simp only [d11552, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11553 q = 1) (hb : d125748 q = 1) : d126292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11553, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11561 q = 1) (hb : d125748 q = 1) : d11561 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11562 q = 1) (hb : d125748 q = 1) : d126297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11562, d126297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11562, d126297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11563 q = 1) (hb : d125748 q = 1) : d126298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11563, d126298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11563, d126298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11564 q = 1) (hb : d125748 q = 1) : d126299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11564, d126299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11564, d126299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11565 q = 1) (hb : d125748 q = 1) : d126300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11565, d126300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11565, d126300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27408 (p : Pattern) (ha : d11598 p = 1) (hb : d125748 p = 1) : d126290 p = 1 := by
  have h0 (q : Pattern) (ha : d11539 q = 1) (hb : d85721 q = 1) : d11539 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11544 q = 1) (hb : d125746 q = 1) : d126288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d125746, d126288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11544, d125746, d126288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11593 q = 1) (hb : d112686 q = 1) : d88705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11593, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25891 q ha hb
    | true =>
      simp only [d11593, d112686, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11594 q = 1) (hb : d112686 q = 1) : d88706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11594, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11594, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11595 q = 1) (hb : d112686 q = 1) : d88707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11595, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11595, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11596 q = 1) (hb : d125747 q = 1) : d88708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11596, d125747, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11596, d125747, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11597 q = 1) (hb : d125748 q = 1) : d126289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11597, d125748, d126289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11597, d125748, d126289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11598 q = 1) (hb : d125748 q = 1) : d126290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11598, d126290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11598, d126290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27409 (p : Pattern) (ha : d11604 p = 1) (hb : d125748 p = 1) : d126306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11599 q = 1) (hb : d125748 q = 1) : d126291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11599, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27408 q ha hb
    | true =>
      simp only [d11599, d126291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11600 q = 1) (hb : d125748 q = 1) : d126292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11600, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11600, d126292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11601 q = 1) (hb : d125748 q = 1) : d126303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11601, d126303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11601, d126303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11602 q = 1) (hb : d125748 q = 1) : d126304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11602, d126304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11602, d126304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11603 q = 1) (hb : d125748 q = 1) : d126305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11603, d126305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11603, d126305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11604 q = 1) (hb : d125748 q = 1) : d126306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11604, d126306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11604, d126306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27410 (p : Pattern) (ha : d108964 p = 1) (hb : d125748 p = 1) : d126312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11566 q = 1) (hb : d125748 q = 1) : d126301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11566, d126301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27406 q ha hb
    | true =>
      simp only [d11566, d126301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27407 q ha hb
  have h2 (q : Pattern) (ha : d108960 q = 1) (hb : d125748 q = 1) : d126302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108960, d126302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108960, d126302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11605 q = 1) (hb : d125748 q = 1) : d126307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11605, d126307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27409 q ha hb
    | true =>
      simp only [d11605, d126307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11606 q = 1) (hb : d125748 q = 1) : d126308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11606, d126308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11606, d126308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108961 q = 1) (hb : d125748 q = 1) : d126309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108961, d126309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108961, d126309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108962 q = 1) (hb : d125748 q = 1) : d126310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108962, d126310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108962, d126310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108963 q = 1) (hb : d125748 q = 1) : d126311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108963, d126311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108963, d126311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108964 q = 1) (hb : d125748 q = 1) : d126312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108964, d126312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108964, d126312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27411 (p : Pattern) (ha : d108970 p = 1) (hb : d125748 p = 1) : d126318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11396 q = 1) (hb : d125748 q = 1) : d126203 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11396, d126203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11396, d126203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27387 q ha hb
  have h2 (q : Pattern) (ha : d11397 q = 1) (hb : d125748 q = 1) : d126204 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11397, d126204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11397, d126204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11406 q = 1) (hb : d125748 q = 1) : d126212 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27387 q ha hb
    | true =>
      simp only [d11406, d126212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27389 q ha hb
  have h4 (q : Pattern) (ha : d11407 q = 1) (hb : d125748 q = 1) : d126213 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11407, d126213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11408 q = 1) (hb : d125748 q = 1) : d126214 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11408, d126214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11408, d126214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108948 q = 1) (hb : d125748 q = 1) : d126268 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108948, d126268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27397 q ha hb
    | true =>
      simp only [d108948, d126268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27402 q ha hb
  have h7 (q : Pattern) (ha : d11519 q = 1) (hb : d125748 q = 1) : d11519 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11520 q = 1) (hb : d125748 q = 1) : d126270 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11520, d126270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27390 q ha hb
    | true =>
      simp only [d11520, d126270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108949 q = 1) (hb : d125748 q = 1) : d126271 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108949, d126271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108949, d126271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108950 q = 1) (hb : d125748 q = 1) : d126272 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108950, d126272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108950, d126272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d108951 q = 1) (hb : d125748 q = 1) : d126273 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108951, d126273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108951, d126273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108955 q = 1) (hb : d125748 q = 1) : d126277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108955, d126277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108955, d126277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27403 q ha hb
  have h13 (q : Pattern) (ha : d11529 q = 1) (hb : d125748 q = 1) : d11529 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d108956 q = 1) (hb : d125748 q = 1) : d126278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108956, d126278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108956, d126278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108957 q = 1) (hb : d125748 q = 1) : d126279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108957, d126279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108957, d126279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d108958 q = 1) (hb : d125748 q = 1) : d126280 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108958, d126280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108958, d126280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d108959 q = 1) (hb : d125748 q = 1) : d126281 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108959, d126281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108959, d126281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d108965 q = 1) (hb : d125748 q = 1) : d126313 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108965, d126313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108965, d126313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27410 q ha hb
  have h19 (q : Pattern) (ha : d11622 q = 1) (hb : d125748 q = 1) : d11622 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d108966 q = 1) (hb : d125748 q = 1) : d126314 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108966, d126314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108966, d126314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d108967 q = 1) (hb : d125748 q = 1) : d126315 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108967, d126315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d108967, d126315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d108968 q = 1) (hb : d125748 q = 1) : d126316 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108968, d126316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108968, d126316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d108969 q = 1) (hb : d125748 q = 1) : d126317 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108969, d126317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d108969, d126317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d108970 q = 1) (hb : d125748 q = 1) : d126318 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108970, d126318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108970, d126318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro27412 (p : Pattern) (ha : d108976 p = 1) (hb : d125748 p = 1) : d126324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d108971 q = 1) (hb : d125748 q = 1) : d126319 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d108971, d126319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108971, d126319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27411 q ha hb
  have h2 (q : Pattern) (ha : d108972 q = 1) (hb : d125748 q = 1) : d126320 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d108972, d126320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108972, d126320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108973 q = 1) (hb : d125748 q = 1) : d126321 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d108973, d126321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108973, d126321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108974 q = 1) (hb : d125748 q = 1) : d126322 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d108974, d126322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108974, d126322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d108975 q = 1) (hb : d125748 q = 1) : d126323 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d108975, d126323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108975, d126323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108976 q = 1) (hb : d125748 q = 1) : d126324 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d108976, d126324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108976, d126324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27413 (p : Pattern) (ha : d11646 p = 1) (hb : d125748 p = 1) : d126330 p = 1 := by
  have h0 (q : Pattern) (ha : d11639 q = 1) (hb : d85721 q = 1) : d11639 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11643 q = 1) (hb : d125746 q = 1) : d126328 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d125746, d126328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11643, d125746, d126328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11640 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12586 q ha hb
    | true =>
      simp only [d11640, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11641 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11641, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11642 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11642, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11644 q = 1) (hb : d125747 q = 1) : d88797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d125747, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11644, d125747, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11645 q = 1) (hb : d125748 q = 1) : d126329 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11645, d125748, d126329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11645, d125748, d126329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11646 q = 1) (hb : d125748 q = 1) : d126330 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11646, d126330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11646, d126330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27414 (p : Pattern) (ha : d11656 p = 1) (hb : d125748 p = 1) : d126336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27413 q ha hb
    | true =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11654 q = 1) (hb : d125748 q = 1) : d126334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11654, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11655 q = 1) (hb : d125748 q = 1) : d126335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11655, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11656 q = 1) (hb : d125748 q = 1) : d126336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11656, d126336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11656, d126336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27415 (p : Pattern) (ha : d11666 p = 1) (hb : d125748 p = 1) : d126342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11660 q = 1) (hb : d125748 q = 1) : d11660 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11661 q = 1) (hb : d125748 q = 1) : d126337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27414 q ha hb
    | true =>
      simp only [d11661, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11662 q = 1) (hb : d125748 q = 1) : d126338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11663 q = 1) (hb : d125748 q = 1) : d126339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11663, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11664 q = 1) (hb : d125748 q = 1) : d126340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11665 q = 1) (hb : d125748 q = 1) : d126341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11666 q = 1) (hb : d125748 q = 1) : d126342 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d126342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11666, d126342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27416 (p : Pattern) (ha : d11669 p = 1) (hb : d125748 p = 1) : d126345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27413 q ha hb
    | true =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11654 q = 1) (hb : d125748 q = 1) : d126334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11654, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11655 q = 1) (hb : d125748 q = 1) : d126335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11655, d126335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11669 q = 1) (hb : d125748 q = 1) : d126345 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11669, d126345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11669, d126345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27417 (p : Pattern) (ha : d11676 p = 1) (hb : d125748 p = 1) : d126351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11660 q = 1) (hb : d125748 q = 1) : d11660 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11661 q = 1) (hb : d125748 q = 1) : d126337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27414 q ha hb
    | true =>
      simp only [d11661, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11662 q = 1) (hb : d125748 q = 1) : d126338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11663 q = 1) (hb : d125748 q = 1) : d126339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11663, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11664 q = 1) (hb : d125748 q = 1) : d126340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11665 q = 1) (hb : d125748 q = 1) : d126341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11670 q = 1) (hb : d125748 q = 1) : d11670 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11671 q = 1) (hb : d125748 q = 1) : d126346 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d126346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27416 q ha hb
    | true =>
      simp only [d11671, d126346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11672 q = 1) (hb : d125748 q = 1) : d126347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d126347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11673 q = 1) (hb : d125748 q = 1) : d126348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11673, d126348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11674 q = 1) (hb : d125748 q = 1) : d126349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d126349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11675 q = 1) (hb : d125748 q = 1) : d126350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d126350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11676 q = 1) (hb : d125748 q = 1) : d126351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d126351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11676, d126351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro27418 (p : Pattern) (ha : d11784 p = 1) (hb : d125748 p = 1) : d126409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11660 q = 1) (hb : d125748 q = 1) : d11660 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11661 q = 1) (hb : d125748 q = 1) : d126337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27414 q ha hb
    | true =>
      simp only [d11661, d126337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11662 q = 1) (hb : d125748 q = 1) : d126338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11662, d126338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11663 q = 1) (hb : d125748 q = 1) : d126339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11663, d126339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11664 q = 1) (hb : d125748 q = 1) : d126340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11664, d126340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11665 q = 1) (hb : d125748 q = 1) : d126341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d126341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11783 q = 1) (hb : d125748 q = 1) : d11783 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11784 q = 1) (hb : d125748 q = 1) : d126409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11784, d126409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11784, d126409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27419 (p : Pattern) (ha : d11681 p = 1) (hb : d125748 p = 1) : d126356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27413 q ha hb
    | true =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11654 q = 1) (hb : d125748 q = 1) : d126334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11654, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11680 q = 1) (hb : d125748 q = 1) : d126355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d126355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d126355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11681 q = 1) (hb : d125748 q = 1) : d126356 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11681, d126356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11681, d126356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27420 (p : Pattern) (ha : d11690 p = 1) (hb : d125748 p = 1) : d126363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27413 q ha hb
    | true =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11688 q = 1) (hb : d125748 q = 1) : d126361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d126361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d126361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11689 q = 1) (hb : d125748 q = 1) : d126362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d126362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11689, d126362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11690 q = 1) (hb : d125748 q = 1) : d126363 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11690, d126363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11690, d126363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27421 (p : Pattern) (ha : d11702 p = 1) (hb : d125748 p = 1) : d126370 p = 1 := by
  have h0 (q : Pattern) (ha : d11699 q = 1) (hb : d85721 q = 1) : d11699 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11639 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11700 q = 1) (hb : d125746 q = 1) : d126367 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11700, d125746, d126367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11700, d125746, d126367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11637 q = 1) (hb : d112686 q = 1) : d114730 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12609 q ha hb
    | true =>
      simp only [d11637, d112686, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11638 q = 1) (hb : d112686 q = 1) : d114731 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11638, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11639 q = 1) (hb : d112686 q = 1) : d114732 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11639, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11642 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d11643 q = 1) (hb : d125747 q = 1) : d126368 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d125747, d126368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11643, d125747, d126368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d11701 q = 1) (hb : d125748 q = 1) : d126369 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11701, d125748, d126369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11701, d125748, d126369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11702 q = 1) (hb : d125748 q = 1) : d126370 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11702, d126370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11702, d126370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27422 (p : Pattern) (ha : d11708 p = 1) (hb : d125748 p = 1) : d126376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d125748 q = 1) : d126371 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d126371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27421 q ha hb
    | true =>
      simp only [d11703, d126371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d125748 q = 1) : d126372 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d126372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d126372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27413 q ha hb
    | true =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d125748 q = 1) : d126373 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d126373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d126373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d125748 q = 1) : d126374 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d126374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d126374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d125748 q = 1) : d126375 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d126375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d126375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11708 q = 1) (hb : d125748 q = 1) : d126376 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11708, d126376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11708, d126376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27423 (p : Pattern) (ha : d11741 p = 1) (hb : d125748 p = 1) : d126330 p = 1 := by
  have h0 (q : Pattern) (ha : d11639 q = 1) (hb : d85721 q = 1) : d11639 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11643 q = 1) (hb : d125746 q = 1) : d126328 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d125746, d126328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11643, d125746, d126328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11736 q = 1) (hb : d112686 q = 1) : d88794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11736, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25917 q ha hb
    | true =>
      simp only [d11736, d112686, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11737 q = 1) (hb : d112686 q = 1) : d88795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11737, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11737, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11738 q = 1) (hb : d112686 q = 1) : d88796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11738, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11738, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11739 q = 1) (hb : d125747 q = 1) : d88797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11739, d125747, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11739, d125747, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11740 q = 1) (hb : d125748 q = 1) : d126329 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11740, d125748, d126329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11740, d125748, d126329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11741 q = 1) (hb : d125748 q = 1) : d126330 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11741, d126330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11741, d126330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27424 (p : Pattern) (ha : d11747 p = 1) (hb : d125748 p = 1) : d126382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27423 q ha hb
    | true =>
      simp only [d11742, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d125748 q = 1) : d126379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d126379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d126379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d125748 q = 1) : d126380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d126380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d126380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d125748 q = 1) : d126381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d126381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d126381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11747 q = 1) (hb : d125748 q = 1) : d126382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11747, d126382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11747, d126382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27425 (p : Pattern) (ha : d108984 p = 1) (hb : d125748 p = 1) : d126388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11683 q = 1) (hb : d125748 q = 1) : d11683 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11684 q = 1) (hb : d125748 q = 1) : d126357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d126357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27419 q ha hb
    | true =>
      simp only [d11684, d126357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11685 q = 1) (hb : d125748 q = 1) : d126358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d126358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d126358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11686 q = 1) (hb : d125748 q = 1) : d126359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d126359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11686, d126359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11687 q = 1) (hb : d125748 q = 1) : d126360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d126360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d126360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11693 q = 1) (hb : d125748 q = 1) : d11693 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11694 q = 1) (hb : d125748 q = 1) : d126364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d126364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27420 q ha hb
    | true =>
      simp only [d11694, d126364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11695 q = 1) (hb : d125748 q = 1) : d126365 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d126365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d126365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11696 q = 1) (hb : d125748 q = 1) : d126366 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d126366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11696, d126366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11709 q = 1) (hb : d125748 q = 1) : d126377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d126377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27422 q ha hb
    | true =>
      simp only [d11709, d126377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27414 q ha hb
  have h11 (q : Pattern) (ha : d108980 q = 1) (hb : d125748 q = 1) : d126378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d126378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108980, d126378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11748 q = 1) (hb : d125748 q = 1) : d126383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d126383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27424 q ha hb
    | true =>
      simp only [d11748, d126383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11749 q = 1) (hb : d125748 q = 1) : d126384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d126384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11749, d126384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108981 q = 1) (hb : d125748 q = 1) : d126385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d126385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108981, d126385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108982 q = 1) (hb : d125748 q = 1) : d126386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d126386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108982, d126386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108983 q = 1) (hb : d125748 q = 1) : d126387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d126387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108983, d126387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d108984 q = 1) (hb : d125748 q = 1) : d126388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108984, d126388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108984, d126388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro27426 (p : Pattern) (ha : d11754 p = 1) (hb : d125748 p = 1) : d126389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27413 q ha hb
    | true =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11654 q = 1) (hb : d125748 q = 1) : d126334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11654, d126334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11680 q = 1) (hb : d125748 q = 1) : d126355 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d126355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11680, d126355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11754 q = 1) (hb : d125748 q = 1) : d126389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11754, d126389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11754, d126389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27427 (p : Pattern) (ha : d11760 p = 1) (hb : d125748 p = 1) : d126394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11647 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27413 q ha hb
    | true =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11648 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11652 q = 1) (hb : d125748 q = 1) : d11652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11653 q = 1) (hb : d125748 q = 1) : d126333 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11653, d126333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11688 q = 1) (hb : d125748 q = 1) : d126361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d126361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11688, d126361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11689 q = 1) (hb : d125748 q = 1) : d126362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d126362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11689, d126362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11760 q = 1) (hb : d125748 q = 1) : d126394 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11760, d126394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11760, d126394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27428 (p : Pattern) (ha : d11765 p = 1) (hb : d125748 p = 1) : d126398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11703 q = 1) (hb : d125748 q = 1) : d126371 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d126371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27421 q ha hb
    | true =>
      simp only [d11703, d126371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11704 q = 1) (hb : d125748 q = 1) : d126372 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d126372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11704, d126372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11647 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27413 q ha hb
    | true =>
      simp only [d11647, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11648 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11648, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11705 q = 1) (hb : d125748 q = 1) : d126373 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d126373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11705, d126373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11706 q = 1) (hb : d125748 q = 1) : d126374 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d126374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11706, d126374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11707 q = 1) (hb : d125748 q = 1) : d126375 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d126375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11707, d126375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11765 q = 1) (hb : d125748 q = 1) : d126398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11765, d126398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11765, d126398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27429 (p : Pattern) (ha : d11771 p = 1) (hb : d125748 p = 1) : d126401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11742 q = 1) (hb : d125748 q = 1) : d126331 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27423 q ha hb
    | true =>
      simp only [d11742, d126331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11743 q = 1) (hb : d125748 q = 1) : d126332 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11743, d126332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11744 q = 1) (hb : d125748 q = 1) : d126379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d126379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11744, d126379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11745 q = 1) (hb : d125748 q = 1) : d126380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d126380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11745, d126380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11746 q = 1) (hb : d125748 q = 1) : d126381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d126381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11746, d126381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11771 q = 1) (hb : d125748 q = 1) : d126401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11771, d126401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11771, d126401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27430 (p : Pattern) (ha : d108989 p = 1) (hb : d125748 p = 1) : d126407 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11683 q = 1) (hb : d125748 q = 1) : d11683 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11684 q = 1) (hb : d125748 q = 1) : d126357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d126357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27419 q ha hb
    | true =>
      simp only [d11684, d126357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11685 q = 1) (hb : d125748 q = 1) : d126358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d126358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11685, d126358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11686 q = 1) (hb : d125748 q = 1) : d126359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d126359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11686, d126359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11687 q = 1) (hb : d125748 q = 1) : d126360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d126360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11687, d126360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11693 q = 1) (hb : d125748 q = 1) : d11693 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11694 q = 1) (hb : d125748 q = 1) : d126364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d126364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27420 q ha hb
    | true =>
      simp only [d11694, d126364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11695 q = 1) (hb : d125748 q = 1) : d126365 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d126365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11695, d126365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11696 q = 1) (hb : d125748 q = 1) : d126366 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d126366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11696, d126366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11709 q = 1) (hb : d125748 q = 1) : d126377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d126377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27422 q ha hb
    | true =>
      simp only [d11709, d126377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27414 q ha hb
  have h11 (q : Pattern) (ha : d108980 q = 1) (hb : d125748 q = 1) : d126378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108980, d126378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108980, d126378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11748 q = 1) (hb : d125748 q = 1) : d126383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d126383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27424 q ha hb
    | true =>
      simp only [d11748, d126383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d11749 q = 1) (hb : d125748 q = 1) : d126384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d126384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11749, d126384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d108981 q = 1) (hb : d125748 q = 1) : d126385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108981, d126385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108981, d126385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108982 q = 1) (hb : d125748 q = 1) : d126386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108982, d126386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108982, d126386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d108983 q = 1) (hb : d125748 q = 1) : d126387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108983, d126387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108983, d126387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11755 q = 1) (hb : d125748 q = 1) : d11755 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d11756 q = 1) (hb : d125748 q = 1) : d126390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11756, d126390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27426 q ha hb
    | true =>
      simp only [d11756, d126390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d11757 q = 1) (hb : d125748 q = 1) : d126391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11757, d126391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11757, d126391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d11758 q = 1) (hb : d125748 q = 1) : d126392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11758, d126392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d11758, d126392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d11759 q = 1) (hb : d125748 q = 1) : d126393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11759, d126393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11759, d126393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d11761 q = 1) (hb : d125748 q = 1) : d11761 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d11762 q = 1) (hb : d125748 q = 1) : d126395 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11762, d126395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27427 q ha hb
    | true =>
      simp only [d11762, d126395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d11763 q = 1) (hb : d125748 q = 1) : d126396 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11763, d126396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11763, d126396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d11764 q = 1) (hb : d125748 q = 1) : d126397 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11764, d126397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d11764, d126397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d11766 q = 1) (hb : d125748 q = 1) : d126399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d126399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27428 q ha hb
    | true =>
      simp only [d11766, d126399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27416 q ha hb
  have h27 (q : Pattern) (ha : d108985 q = 1) (hb : d125748 q = 1) : d126400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d126400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d108985, d126400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d11772 q = 1) (hb : d125748 q = 1) : d126402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d126402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27429 q ha hb
    | true =>
      simp only [d11772, d126402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d11773 q = 1) (hb : d125748 q = 1) : d126403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d126403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d11773, d126403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d108986 q = 1) (hb : d125748 q = 1) : d126404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d126404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d108986, d126404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d108987 q = 1) (hb : d125748 q = 1) : d126405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108987, d126405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d108987, d126405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d108988 q = 1) (hb : d125748 q = 1) : d126406 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108988, d126406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d108988, d126406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d108989 q = 1) (hb : d125748 q = 1) : d126407 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108989, d126407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108989, d126407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro27431 (p : Pattern) (ha : d108996 p = 1) (hb : d125748 p = 1) : d126416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11766 q = 1) (hb : d125748 q = 1) : d126399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d126399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27428 q ha hb
    | true =>
      simp only [d11766, d126399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27416 q ha hb
  have h2 (q : Pattern) (ha : d108985 q = 1) (hb : d125748 q = 1) : d126400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108985, d126400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108985, d126400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11772 q = 1) (hb : d125748 q = 1) : d126402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d126402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27429 q ha hb
    | true =>
      simp only [d11772, d126402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11773 q = 1) (hb : d125748 q = 1) : d126403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d126403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11773, d126403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d108986 q = 1) (hb : d125748 q = 1) : d126404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108986, d126404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108986, d126404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108994 q = 1) (hb : d125748 q = 1) : d126414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108994, d126414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108994, d126414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108995 q = 1) (hb : d125748 q = 1) : d126415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108995, d126415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108995, d126415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108996 q = 1) (hb : d125748 q = 1) : d126416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108996, d126416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108996, d126416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27432 (p : Pattern) (ha : d11817 p = 1) (hb : d125748 p = 1) : d126425 p = 1 := by
  have h0 (q : Pattern) (ha : d11807 q = 1) (hb : d85721 q = 1) : d11807 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11811 q = 1) (hb : d125746 q = 1) : d126422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11811, d125746, d126422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11811, d125746, d126422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11808 q = 1) (hb : d112686 q = 1) : d114787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12627 q ha hb
    | true =>
      simp only [d11808, d112686, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11809 q = 1) (hb : d112686 q = 1) : d114788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11809, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11810 q = 1) (hb : d112686 q = 1) : d114789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11810, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11814 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d11815 q = 1) (hb : d125747 q = 1) : d126423 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d125747, d126423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11815, d125747, d126423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d11816 q = 1) (hb : d125748 q = 1) : d126424 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11816, d125748, d126424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11816, d125748, d126424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11817 q = 1) (hb : d125748 q = 1) : d126425 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11817, d126425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11817, d126425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27433 (p : Pattern) (ha : d11822 p = 1) (hb : d125748 p = 1) : d126430 p = 1 := by
  have h0 (q : Pattern) (ha : d11810 q = 1) (hb : d85721 q = 1) : d11810 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11814 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11815 q = 1) (hb : d125746 q = 1) : d126428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d125746, d126428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11815, d125746, d126428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11812 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12623 q ha hb
    | true =>
      simp only [d11812, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11813 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11813, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11814 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11814, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11820 q = 1) (hb : d125747 q = 1) : d88861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d125747, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11820, d125747, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11821 q = 1) (hb : d125748 q = 1) : d126429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11821, d125748, d126429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11821, d125748, d126429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11822 q = 1) (hb : d125748 q = 1) : d126430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11822, d126430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11822, d126430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27434 (p : Pattern) (ha : d11828 p = 1) (hb : d125748 p = 1) : d126436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11818 q = 1) (hb : d125748 q = 1) : d126426 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11818, d126426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27432 q ha hb
    | true =>
      simp only [d11818, d126426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11819 q = 1) (hb : d125748 q = 1) : d126427 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11819, d126427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11819, d126427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11823 q = 1) (hb : d125748 q = 1) : d126431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27433 q ha hb
    | true =>
      simp only [d11823, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11824 q = 1) (hb : d125748 q = 1) : d126432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11825 q = 1) (hb : d125748 q = 1) : d126433 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11825, d126433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11825, d126433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11826 q = 1) (hb : d125748 q = 1) : d126434 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11826, d126434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11826, d126434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11827 q = 1) (hb : d125748 q = 1) : d126435 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11827, d126435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11827, d126435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11828 q = 1) (hb : d125748 q = 1) : d126436 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11828, d126436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11828, d126436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27435 (p : Pattern) (ha : d11836 p = 1) (hb : d125748 p = 1) : d126440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11823 q = 1) (hb : d125748 q = 1) : d126431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27433 q ha hb
    | true =>
      simp only [d11823, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11824 q = 1) (hb : d125748 q = 1) : d126432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11824, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11832 q = 1) (hb : d125748 q = 1) : d11832 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11833 q = 1) (hb : d125748 q = 1) : d126437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11833, d126437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11833, d126437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11834 q = 1) (hb : d125748 q = 1) : d126438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11834, d126438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11834, d126438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11835 q = 1) (hb : d125748 q = 1) : d126439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11835, d126439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11835, d126439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11836 q = 1) (hb : d125748 q = 1) : d126440 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11836, d126440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11836, d126440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27436 (p : Pattern) (ha : d11869 p = 1) (hb : d125748 p = 1) : d126430 p = 1 := by
  have h0 (q : Pattern) (ha : d11810 q = 1) (hb : d85721 q = 1) : d11810 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11814 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11815 q = 1) (hb : d125746 q = 1) : d126428 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d125746, d126428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11815, d125746, d126428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11864 q = 1) (hb : d112686 q = 1) : d88858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11864, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25933 q ha hb
    | true =>
      simp only [d11864, d112686, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11865 q = 1) (hb : d112686 q = 1) : d88859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11865, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11865, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11866 q = 1) (hb : d112686 q = 1) : d88860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11866, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11866, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11867 q = 1) (hb : d125747 q = 1) : d88861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11867, d125747, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11867, d125747, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11868 q = 1) (hb : d125748 q = 1) : d126429 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11868, d125748, d126429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11868, d125748, d126429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11869 q = 1) (hb : d125748 q = 1) : d126430 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11869, d126430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11869, d126430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27437 (p : Pattern) (ha : d11875 p = 1) (hb : d125748 p = 1) : d126446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11870 q = 1) (hb : d125748 q = 1) : d126431 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11870, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27436 q ha hb
    | true =>
      simp only [d11870, d126431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11871 q = 1) (hb : d125748 q = 1) : d126432 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11871, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11871, d126432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11872 q = 1) (hb : d125748 q = 1) : d126443 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11872, d126443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11872, d126443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11873 q = 1) (hb : d125748 q = 1) : d126444 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11873, d126444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11873, d126444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11874 q = 1) (hb : d125748 q = 1) : d126445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11874, d126445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11874, d126445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11875 q = 1) (hb : d125748 q = 1) : d126446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11875, d126446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11875, d126446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27438 (p : Pattern) (ha : d109006 p = 1) (hb : d125748 p = 1) : d126452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11837 q = 1) (hb : d125748 q = 1) : d126441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11837, d126441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27434 q ha hb
    | true =>
      simp only [d11837, d126441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27435 q ha hb
  have h2 (q : Pattern) (ha : d109002 q = 1) (hb : d125748 q = 1) : d126442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109002, d126442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109002, d126442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11876 q = 1) (hb : d125748 q = 1) : d126447 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11876, d126447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27437 q ha hb
    | true =>
      simp only [d11876, d126447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11877 q = 1) (hb : d125748 q = 1) : d126448 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11877, d126448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11877, d126448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109003 q = 1) (hb : d125748 q = 1) : d126449 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109003, d126449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109003, d126449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109004 q = 1) (hb : d125748 q = 1) : d126450 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109004, d126450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109004, d126450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109005 q = 1) (hb : d125748 q = 1) : d126451 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109005, d126451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109005, d126451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109006 q = 1) (hb : d125748 q = 1) : d126452 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109006, d126452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109006, d126452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27439 (p : Pattern) (ha : d109012 p = 1) (hb : d125748 p = 1) : d126458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11667 q = 1) (hb : d125748 q = 1) : d126343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11667, d126343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11667, d126343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27415 q ha hb
  have h2 (q : Pattern) (ha : d11668 q = 1) (hb : d125748 q = 1) : d126344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11668, d126344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11668, d126344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11677 q = 1) (hb : d125748 q = 1) : d126352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27415 q ha hb
    | true =>
      simp only [d11677, d126352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27417 q ha hb
  have h4 (q : Pattern) (ha : d11678 q = 1) (hb : d125748 q = 1) : d126353 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11678, d126353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11679 q = 1) (hb : d125748 q = 1) : d126354 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11679, d126354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11679, d126354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108990 q = 1) (hb : d125748 q = 1) : d126408 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108990, d126408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27425 q ha hb
    | true =>
      simp only [d108990, d126408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27430 q ha hb
  have h7 (q : Pattern) (ha : d11790 q = 1) (hb : d125748 q = 1) : d11790 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11791 q = 1) (hb : d125748 q = 1) : d126410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11791, d126410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27418 q ha hb
    | true =>
      simp only [d11791, d126410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d108991 q = 1) (hb : d125748 q = 1) : d126411 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108991, d126411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108991, d126411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d108992 q = 1) (hb : d125748 q = 1) : d126412 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108992, d126412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108992, d126412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d108993 q = 1) (hb : d125748 q = 1) : d126413 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108993, d126413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d108993, d126413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d108997 q = 1) (hb : d125748 q = 1) : d126417 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108997, d126417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108997, d126417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27431 q ha hb
  have h13 (q : Pattern) (ha : d11800 q = 1) (hb : d125748 q = 1) : d11800 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d108998 q = 1) (hb : d125748 q = 1) : d126418 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108998, d126418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108998, d126418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d108999 q = 1) (hb : d125748 q = 1) : d126419 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108999, d126419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108999, d126419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d109000 q = 1) (hb : d125748 q = 1) : d126420 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109000, d126420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109000, d126420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d109001 q = 1) (hb : d125748 q = 1) : d126421 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109001, d126421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109001, d126421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d109007 q = 1) (hb : d125748 q = 1) : d126453 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109007, d126453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109007, d126453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27438 q ha hb
  have h19 (q : Pattern) (ha : d11893 q = 1) (hb : d125748 q = 1) : d11893 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d109008 q = 1) (hb : d125748 q = 1) : d126454 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109008, d126454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109008, d126454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d109009 q = 1) (hb : d125748 q = 1) : d126455 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109009, d126455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d109009, d126455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d109010 q = 1) (hb : d125748 q = 1) : d126456 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109010, d126456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109010, d126456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d109011 q = 1) (hb : d125748 q = 1) : d126457 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109011, d126457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d109011, d126457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d109012 q = 1) (hb : d125748 q = 1) : d126458 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109012, d126458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109012, d126458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro27440 (p : Pattern) (ha : d109018 p = 1) (hb : d125748 p = 1) : d126464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109013 q = 1) (hb : d125748 q = 1) : d126459 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109013, d126459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109013, d126459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27439 q ha hb
  have h2 (q : Pattern) (ha : d109014 q = 1) (hb : d125748 q = 1) : d126460 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109014, d126460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109014, d126460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109015 q = 1) (hb : d125748 q = 1) : d126461 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109015, d126461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109015, d126461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109016 q = 1) (hb : d125748 q = 1) : d126462 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109016, d126462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109016, d126462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109017 q = 1) (hb : d125748 q = 1) : d126463 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109017, d126463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109017, d126463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109018 q = 1) (hb : d125748 q = 1) : d126464 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109018, d126464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109018, d126464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27441 (p : Pattern) (ha : d11918 p = 1) (hb : d125748 p = 1) : d126471 p = 1 := by
  have h0 (q : Pattern) (ha : d11911 q = 1) (hb : d85721 q = 1) : d11911 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11914 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11915 q = 1) (hb : d125746 q = 1) : d126469 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d125746, d126469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11915, d125746, d126469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11912 q = 1) (hb : d112686 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12636 q ha hb
    | true =>
      simp only [d11912, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11913 q = 1) (hb : d112686 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11913, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11914 q = 1) (hb : d112686 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11914, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11916 q = 1) (hb : d125747 q = 1) : d88951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d125747, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11916, d125747, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d11917 q = 1) (hb : d125748 q = 1) : d126470 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11917, d125748, d126470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11917, d125748, d126470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d11918 q = 1) (hb : d125748 q = 1) : d126471 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11918, d126471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11918, d126471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27442 (p : Pattern) (ha : d11928 p = 1) (hb : d125748 p = 1) : d126477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d125748 q = 1) : d126472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27441 q ha hb
    | true =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d125748 q = 1) : d126473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d125748 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d125748 q = 1) : d126474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11926 q = 1) (hb : d125748 q = 1) : d126475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d126475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11926, d126475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11927 q = 1) (hb : d125748 q = 1) : d126476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d126476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11927, d126476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11928 q = 1) (hb : d125748 q = 1) : d126477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11928, d126477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11928, d126477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27443 (p : Pattern) (ha : d11938 p = 1) (hb : d125748 p = 1) : d126483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11932 q = 1) (hb : d125748 q = 1) : d11932 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11933 q = 1) (hb : d125748 q = 1) : d126478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d126478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27442 q ha hb
    | true =>
      simp only [d11933, d126478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11934 q = 1) (hb : d125748 q = 1) : d126479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11935 q = 1) (hb : d125748 q = 1) : d126480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11935, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11936 q = 1) (hb : d125748 q = 1) : d126481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11937 q = 1) (hb : d125748 q = 1) : d126482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11938 q = 1) (hb : d125748 q = 1) : d126483 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11938, d126483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11938, d126483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27444 (p : Pattern) (ha : d11941 p = 1) (hb : d125748 p = 1) : d126486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d125748 q = 1) : d126472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27441 q ha hb
    | true =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d125748 q = 1) : d126473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d125748 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d125748 q = 1) : d126474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11926 q = 1) (hb : d125748 q = 1) : d126475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d126475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11926, d126475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11927 q = 1) (hb : d125748 q = 1) : d126476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d126476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11927, d126476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11941 q = 1) (hb : d125748 q = 1) : d126486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11941, d126486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11941, d126486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27445 (p : Pattern) (ha : d11948 p = 1) (hb : d125748 p = 1) : d126492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11932 q = 1) (hb : d125748 q = 1) : d11932 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11933 q = 1) (hb : d125748 q = 1) : d126478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d126478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27442 q ha hb
    | true =>
      simp only [d11933, d126478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11934 q = 1) (hb : d125748 q = 1) : d126479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11935 q = 1) (hb : d125748 q = 1) : d126480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11935, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11936 q = 1) (hb : d125748 q = 1) : d126481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11937 q = 1) (hb : d125748 q = 1) : d126482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11942 q = 1) (hb : d125748 q = 1) : d11942 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d11943 q = 1) (hb : d125748 q = 1) : d126487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d126487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27444 q ha hb
    | true =>
      simp only [d11943, d126487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11944 q = 1) (hb : d125748 q = 1) : d126488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d126488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11945 q = 1) (hb : d125748 q = 1) : d126489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11945, d126489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d11946 q = 1) (hb : d125748 q = 1) : d126490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d126490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11947 q = 1) (hb : d125748 q = 1) : d126491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d126491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11948 q = 1) (hb : d125748 q = 1) : d126492 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11948, d126492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11948, d126492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro27446 (p : Pattern) (ha : d12056 p = 1) (hb : d125748 p = 1) : d126550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11932 q = 1) (hb : d125748 q = 1) : d11932 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11933 q = 1) (hb : d125748 q = 1) : d126478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d126478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27442 q ha hb
    | true =>
      simp only [d11933, d126478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11934 q = 1) (hb : d125748 q = 1) : d126479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11934, d126479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11935 q = 1) (hb : d125748 q = 1) : d126480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11935, d126480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11936 q = 1) (hb : d125748 q = 1) : d126481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11936, d126481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11937 q = 1) (hb : d125748 q = 1) : d126482 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d126482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12055 q = 1) (hb : d125748 q = 1) : d12055 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12056 q = 1) (hb : d125748 q = 1) : d126550 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12056, d126550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12056, d126550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27447 (p : Pattern) (ha : d11953 p = 1) (hb : d125748 p = 1) : d126497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d125748 q = 1) : d126472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27441 q ha hb
    | true =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d125748 q = 1) : d126473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d125748 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d125748 q = 1) : d126474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11926 q = 1) (hb : d125748 q = 1) : d126475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d126475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11926, d126475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11952 q = 1) (hb : d125748 q = 1) : d126496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d126496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d126496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11953 q = 1) (hb : d125748 q = 1) : d126497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11953, d126497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11953, d126497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27448 (p : Pattern) (ha : d11962 p = 1) (hb : d125748 p = 1) : d126504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d125748 q = 1) : d126472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27441 q ha hb
    | true =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d125748 q = 1) : d126473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d125748 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d125748 q = 1) : d126474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11960 q = 1) (hb : d125748 q = 1) : d126502 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d126502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d126502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11961 q = 1) (hb : d125748 q = 1) : d126503 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d126503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11961, d126503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11962 q = 1) (hb : d125748 q = 1) : d126504 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11962, d126504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11962, d126504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro27449 (p : Pattern) (ha : d11974 p = 1) (hb : d125748 p = 1) : d126511 p = 1 := by
  have h0 (q : Pattern) (ha : d11971 q = 1) (hb : d85721 q = 1) : d11971 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11911 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11972 q = 1) (hb : d125746 q = 1) : d126508 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11972, d125746, d126508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11972, d125746, d126508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11909 q = 1) (hb : d112686 q = 1) : d114875 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12659 q ha hb
    | true =>
      simp only [d11909, d112686, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11910 q = 1) (hb : d112686 q = 1) : d114876 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11910, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11911 q = 1) (hb : d112686 q = 1) : d114877 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11911, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11914 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d11915 q = 1) (hb : d125747 q = 1) : d126509 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d125747, d126509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11915, d125747, d126509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d11973 q = 1) (hb : d125748 q = 1) : d126510 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11973, d125748, d126510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11973, d125748, d126510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d11974 q = 1) (hb : d125748 q = 1) : d126511 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11974, d126511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11974, d126511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27450 (p : Pattern) (ha : d11980 p = 1) (hb : d125748 p = 1) : d126517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d125748 q = 1) : d126512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d126512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27449 q ha hb
    | true =>
      simp only [d11975, d126512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d125748 q = 1) : d126513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d126513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d126513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11919 q = 1) (hb : d125748 q = 1) : d126472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27441 q ha hb
    | true =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11920 q = 1) (hb : d125748 q = 1) : d126473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d125748 q = 1) : d126514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d126514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d126514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d125748 q = 1) : d126515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d126515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d126515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d125748 q = 1) : d126516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d126516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d126516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11980 q = 1) (hb : d125748 q = 1) : d126517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11980, d126517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11980, d126517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27451 (p : Pattern) (ha : d12013 p = 1) (hb : d125748 p = 1) : d126471 p = 1 := by
  have h0 (q : Pattern) (ha : d11911 q = 1) (hb : d85721 q = 1) : d11911 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11914 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11915 q = 1) (hb : d125746 q = 1) : d126469 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d125746, d126469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11915, d125746, d126469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12008 q = 1) (hb : d112686 q = 1) : d88948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12008, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25959 q ha hb
    | true =>
      simp only [d12008, d112686, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12009 q = 1) (hb : d112686 q = 1) : d88949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12009, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12009, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12010 q = 1) (hb : d112686 q = 1) : d88950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12010, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12010, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12011 q = 1) (hb : d125747 q = 1) : d88951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12011, d125747, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12011, d125747, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d12012 q = 1) (hb : d125748 q = 1) : d126470 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12012, d125748, d126470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12012, d125748, d126470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12013 q = 1) (hb : d125748 q = 1) : d126471 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12013, d126471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12013, d126471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27452 (p : Pattern) (ha : d12019 p = 1) (hb : d125748 p = 1) : d126523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d125748 q = 1) : d126472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27451 q ha hb
    | true =>
      simp only [d12014, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d125748 q = 1) : d126473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12016 q = 1) (hb : d125748 q = 1) : d126520 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d126520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d126520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12017 q = 1) (hb : d125748 q = 1) : d126521 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d126521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12017, d126521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12018 q = 1) (hb : d125748 q = 1) : d126522 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d126522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12018, d126522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12019 q = 1) (hb : d125748 q = 1) : d126523 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12019, d126523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12019, d126523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27453 (p : Pattern) (ha : d109027 p = 1) (hb : d125748 p = 1) : d126529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11955 q = 1) (hb : d125748 q = 1) : d11955 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11956 q = 1) (hb : d125748 q = 1) : d126498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d126498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27447 q ha hb
    | true =>
      simp only [d11956, d126498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11957 q = 1) (hb : d125748 q = 1) : d126499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d126499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d126499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11958 q = 1) (hb : d125748 q = 1) : d126500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d126500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11958, d126500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11959 q = 1) (hb : d125748 q = 1) : d126501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d126501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d126501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11965 q = 1) (hb : d125748 q = 1) : d11965 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11966 q = 1) (hb : d125748 q = 1) : d126505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d126505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27448 q ha hb
    | true =>
      simp only [d11966, d126505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11967 q = 1) (hb : d125748 q = 1) : d126506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d126506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d126506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11968 q = 1) (hb : d125748 q = 1) : d126507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d126507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11968, d126507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11981 q = 1) (hb : d125748 q = 1) : d126518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d126518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27450 q ha hb
    | true =>
      simp only [d11981, d126518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27442 q ha hb
  have h11 (q : Pattern) (ha : d109023 q = 1) (hb : d125748 q = 1) : d126519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d126519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109023, d126519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12020 q = 1) (hb : d125748 q = 1) : d126524 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d126524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27452 q ha hb
    | true =>
      simp only [d12020, d126524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12021 q = 1) (hb : d125748 q = 1) : d126525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d126525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12021, d126525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109024 q = 1) (hb : d125748 q = 1) : d126526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d126526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109024, d126526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109025 q = 1) (hb : d125748 q = 1) : d126527 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d126527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109025, d126527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109026 q = 1) (hb : d125748 q = 1) : d126528 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d126528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109026, d126528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109027 q = 1) (hb : d125748 q = 1) : d126529 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109027, d126529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109027, d126529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro27454 (p : Pattern) (ha : d12026 p = 1) (hb : d125748 p = 1) : d126530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d125748 q = 1) : d126472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27441 q ha hb
    | true =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d125748 q = 1) : d126473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d125748 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d125748 q = 1) : d126474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11926 q = 1) (hb : d125748 q = 1) : d126475 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d126475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11926, d126475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11952 q = 1) (hb : d125748 q = 1) : d126496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d126496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11952, d126496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12026 q = 1) (hb : d125748 q = 1) : d126530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12026, d126530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12026, d126530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27455 (p : Pattern) (ha : d12032 p = 1) (hb : d125748 p = 1) : d126535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11919 q = 1) (hb : d125748 q = 1) : d126472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27441 q ha hb
    | true =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11920 q = 1) (hb : d125748 q = 1) : d126473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11924 q = 1) (hb : d125748 q = 1) : d11924 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11925 q = 1) (hb : d125748 q = 1) : d126474 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11925, d126474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11960 q = 1) (hb : d125748 q = 1) : d126502 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d126502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11960, d126502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11961 q = 1) (hb : d125748 q = 1) : d126503 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d126503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11961, d126503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12032 q = 1) (hb : d125748 q = 1) : d126535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12032, d126535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12032, d126535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27456 (p : Pattern) (ha : d12037 p = 1) (hb : d125748 p = 1) : d126539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11975 q = 1) (hb : d125748 q = 1) : d126512 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d126512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27449 q ha hb
    | true =>
      simp only [d11975, d126512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11976 q = 1) (hb : d125748 q = 1) : d126513 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d126513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11976, d126513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11919 q = 1) (hb : d125748 q = 1) : d126472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27441 q ha hb
    | true =>
      simp only [d11919, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11920 q = 1) (hb : d125748 q = 1) : d126473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11920, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11977 q = 1) (hb : d125748 q = 1) : d126514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d126514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11977, d126514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11978 q = 1) (hb : d125748 q = 1) : d126515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d126515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11978, d126515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11979 q = 1) (hb : d125748 q = 1) : d126516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d126516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11979, d126516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12037 q = 1) (hb : d125748 q = 1) : d126539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12037, d126539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12037, d126539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27457 (p : Pattern) (ha : d12043 p = 1) (hb : d125748 p = 1) : d126542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12014 q = 1) (hb : d125748 q = 1) : d126472 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27451 q ha hb
    | true =>
      simp only [d12014, d126472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12015 q = 1) (hb : d125748 q = 1) : d126473 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12015, d126473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12016 q = 1) (hb : d125748 q = 1) : d126520 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d126520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12016, d126520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12017 q = 1) (hb : d125748 q = 1) : d126521 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d126521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12017, d126521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12018 q = 1) (hb : d125748 q = 1) : d126522 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d126522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12018, d126522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12043 q = 1) (hb : d125748 q = 1) : d126542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12043, d126542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12043, d126542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27458 (p : Pattern) (ha : d109032 p = 1) (hb : d125748 p = 1) : d126548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11955 q = 1) (hb : d125748 q = 1) : d11955 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11956 q = 1) (hb : d125748 q = 1) : d126498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d126498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27447 q ha hb
    | true =>
      simp only [d11956, d126498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11957 q = 1) (hb : d125748 q = 1) : d126499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d126499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11957, d126499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11958 q = 1) (hb : d125748 q = 1) : d126500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d126500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11958, d126500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11959 q = 1) (hb : d125748 q = 1) : d126501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d126501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11959, d126501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11965 q = 1) (hb : d125748 q = 1) : d11965 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11966 q = 1) (hb : d125748 q = 1) : d126505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d126505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27448 q ha hb
    | true =>
      simp only [d11966, d126505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11967 q = 1) (hb : d125748 q = 1) : d126506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d126506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11967, d126506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11968 q = 1) (hb : d125748 q = 1) : d126507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d126507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11968, d126507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d11981 q = 1) (hb : d125748 q = 1) : d126518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d126518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27450 q ha hb
    | true =>
      simp only [d11981, d126518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27442 q ha hb
  have h11 (q : Pattern) (ha : d109023 q = 1) (hb : d125748 q = 1) : d126519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109023, d126519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109023, d126519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12020 q = 1) (hb : d125748 q = 1) : d126524 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d126524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27452 q ha hb
    | true =>
      simp only [d12020, d126524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12021 q = 1) (hb : d125748 q = 1) : d126525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d126525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12021, d126525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109024 q = 1) (hb : d125748 q = 1) : d126526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109024, d126526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109024, d126526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109025 q = 1) (hb : d125748 q = 1) : d126527 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109025, d126527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109025, d126527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109026 q = 1) (hb : d125748 q = 1) : d126528 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109026, d126528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109026, d126528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12027 q = 1) (hb : d125748 q = 1) : d12027 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12028 q = 1) (hb : d125748 q = 1) : d126531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12028, d126531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27454 q ha hb
    | true =>
      simp only [d12028, d126531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12029 q = 1) (hb : d125748 q = 1) : d126532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12029, d126532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12029, d126532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12030 q = 1) (hb : d125748 q = 1) : d126533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12030, d126533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12030, d126533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12031 q = 1) (hb : d125748 q = 1) : d126534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12031, d126534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12031, d126534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12033 q = 1) (hb : d125748 q = 1) : d12033 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12034 q = 1) (hb : d125748 q = 1) : d126536 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12034, d126536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27455 q ha hb
    | true =>
      simp only [d12034, d126536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12035 q = 1) (hb : d125748 q = 1) : d126537 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12035, d126537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12035, d126537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12036 q = 1) (hb : d125748 q = 1) : d126538 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12036, d126538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12036, d126538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12038 q = 1) (hb : d125748 q = 1) : d126540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d126540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27456 q ha hb
    | true =>
      simp only [d12038, d126540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27444 q ha hb
  have h27 (q : Pattern) (ha : d109028 q = 1) (hb : d125748 q = 1) : d126541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d126541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d109028, d126541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d12044 q = 1) (hb : d125748 q = 1) : d126543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d126543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27457 q ha hb
    | true =>
      simp only [d12044, d126543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12045 q = 1) (hb : d125748 q = 1) : d126544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d126544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12045, d126544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d109029 q = 1) (hb : d125748 q = 1) : d126545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d126545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d109029, d126545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d109030 q = 1) (hb : d125748 q = 1) : d126546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109030, d126546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d109030, d126546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d109031 q = 1) (hb : d125748 q = 1) : d126547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109031, d126547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109031, d126547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d109032 q = 1) (hb : d125748 q = 1) : d126548 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109032, d126548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109032, d126548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro27459 (p : Pattern) (ha : d109039 p = 1) (hb : d125748 p = 1) : d126557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12038 q = 1) (hb : d125748 q = 1) : d126540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d126540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27456 q ha hb
    | true =>
      simp only [d12038, d126540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27444 q ha hb
  have h2 (q : Pattern) (ha : d109028 q = 1) (hb : d125748 q = 1) : d126541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109028, d126541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109028, d126541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12044 q = 1) (hb : d125748 q = 1) : d126543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d126543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27457 q ha hb
    | true =>
      simp only [d12044, d126543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12045 q = 1) (hb : d125748 q = 1) : d126544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d126544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12045, d126544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109029 q = 1) (hb : d125748 q = 1) : d126545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109029, d126545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109029, d126545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109037 q = 1) (hb : d125748 q = 1) : d126555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109037, d126555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109037, d126555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109038 q = 1) (hb : d125748 q = 1) : d126556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109038, d126556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109038, d126556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109039 q = 1) (hb : d125748 q = 1) : d126557 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109039, d126557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109039, d126557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27460 (p : Pattern) (ha : d12089 p = 1) (hb : d125748 p = 1) : d126566 p = 1 := by
  have h0 (q : Pattern) (ha : d12079 q = 1) (hb : d85721 q = 1) : d12079 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12082 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12083 q = 1) (hb : d125746 q = 1) : d126563 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12083, d125746, d126563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12083, d125746, d126563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12080 q = 1) (hb : d112686 q = 1) : d114932 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12677 q ha hb
    | true =>
      simp only [d12080, d112686, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12081 q = 1) (hb : d112686 q = 1) : d114933 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12081, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12082 q = 1) (hb : d112686 q = 1) : d114934 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12082, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12086 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d12087 q = 1) (hb : d125747 q = 1) : d126564 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d125747, d126564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12087, d125747, d126564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d12088 q = 1) (hb : d125748 q = 1) : d126565 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12088, d125748, d126565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12088, d125748, d126565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d12089 q = 1) (hb : d125748 q = 1) : d126566 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12089, d126566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12089, d126566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro27461 (p : Pattern) (ha : d12094 p = 1) (hb : d125748 p = 1) : d126571 p = 1 := by
  have h0 (q : Pattern) (ha : d12082 q = 1) (hb : d85721 q = 1) : d12082 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12087 q = 1) (hb : d125746 q = 1) : d126569 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d125746, d126569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12087, d125746, d126569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12084 q = 1) (hb : d112686 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12673 q ha hb
    | true =>
      simp only [d12084, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12085 q = 1) (hb : d112686 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12085, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12086 q = 1) (hb : d112686 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12086, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12092 q = 1) (hb : d125747 q = 1) : d89015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d125747, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12092, d125747, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d12093 q = 1) (hb : d125748 q = 1) : d126570 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12093, d125748, d126570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12093, d125748, d126570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12094 q = 1) (hb : d125748 q = 1) : d126571 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12094, d126571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12094, d126571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27462 (p : Pattern) (ha : d12100 p = 1) (hb : d125748 p = 1) : d126577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12090 q = 1) (hb : d125748 q = 1) : d126567 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12090, d126567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27460 q ha hb
    | true =>
      simp only [d12090, d126567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12091 q = 1) (hb : d125748 q = 1) : d126568 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12091, d126568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12091, d126568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12095 q = 1) (hb : d125748 q = 1) : d126572 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d126572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27461 q ha hb
    | true =>
      simp only [d12095, d126572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12096 q = 1) (hb : d125748 q = 1) : d126573 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d126573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d126573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12097 q = 1) (hb : d125748 q = 1) : d126574 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12097, d126574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12097, d126574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12098 q = 1) (hb : d125748 q = 1) : d126575 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12098, d126575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12098, d126575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12099 q = 1) (hb : d125748 q = 1) : d126576 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12099, d126576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12099, d126576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12100 q = 1) (hb : d125748 q = 1) : d126577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12100, d126577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12100, d126577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro27463 (p : Pattern) (ha : d12108 p = 1) (hb : d125748 p = 1) : d126581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12095 q = 1) (hb : d125748 q = 1) : d126572 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d126572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27461 q ha hb
    | true =>
      simp only [d12095, d126572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12096 q = 1) (hb : d125748 q = 1) : d126573 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d126573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12096, d126573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12104 q = 1) (hb : d125748 q = 1) : d12104 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12105 q = 1) (hb : d125748 q = 1) : d126578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12105, d126578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12105, d126578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12106 q = 1) (hb : d125748 q = 1) : d126579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12106, d126579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12106, d126579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12107 q = 1) (hb : d125748 q = 1) : d126580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12107, d126580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12107, d126580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12108 q = 1) (hb : d125748 q = 1) : d126581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12108, d126581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12108, d126581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro27464 (p : Pattern) (ha : d12141 p = 1) (hb : d125748 p = 1) : d126571 p = 1 := by
  have h0 (q : Pattern) (ha : d12082 q = 1) (hb : d85721 q = 1) : d12082 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12087 q = 1) (hb : d125746 q = 1) : d126569 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d125746, d126569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12087, d125746, d126569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12136 q = 1) (hb : d112686 q = 1) : d89012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12136, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25975 q ha hb
    | true =>
      simp only [d12136, d112686, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12137 q = 1) (hb : d112686 q = 1) : d89013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12137, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12137, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12138 q = 1) (hb : d112686 q = 1) : d89014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12138, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12138, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12139 q = 1) (hb : d125747 q = 1) : d89015 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12139, d125747, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12139, d125747, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d12140 q = 1) (hb : d125748 q = 1) : d126570 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12140, d125748, d126570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12140, d125748, d126570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12141 q = 1) (hb : d125748 q = 1) : d126571 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12141, d126571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12141, d126571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27465 (p : Pattern) (ha : d12147 p = 1) (hb : d125748 p = 1) : d126587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12142 q = 1) (hb : d125748 q = 1) : d126572 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12142, d126572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27464 q ha hb
    | true =>
      simp only [d12142, d126572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12143 q = 1) (hb : d125748 q = 1) : d126573 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12143, d126573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12143, d126573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12144 q = 1) (hb : d125748 q = 1) : d126584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12144, d126584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12144, d126584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12145 q = 1) (hb : d125748 q = 1) : d126585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12145, d126585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12145, d126585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12146 q = 1) (hb : d125748 q = 1) : d126586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12146, d126586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12146, d126586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12147 q = 1) (hb : d125748 q = 1) : d126587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12147, d126587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12147, d126587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27466 (p : Pattern) (ha : d109049 p = 1) (hb : d125748 p = 1) : d126593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12109 q = 1) (hb : d125748 q = 1) : d126582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12109, d126582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27462 q ha hb
    | true =>
      simp only [d12109, d126582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27463 q ha hb
  have h2 (q : Pattern) (ha : d109045 q = 1) (hb : d125748 q = 1) : d126583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109045, d126583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109045, d126583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12148 q = 1) (hb : d125748 q = 1) : d126588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12148, d126588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27465 q ha hb
    | true =>
      simp only [d12148, d126588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12149 q = 1) (hb : d125748 q = 1) : d126589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12149, d126589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12149, d126589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109046 q = 1) (hb : d125748 q = 1) : d126590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109046, d126590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109046, d126590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109047 q = 1) (hb : d125748 q = 1) : d126591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109047, d126591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109047, d126591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109048 q = 1) (hb : d125748 q = 1) : d126592 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109048, d126592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109048, d126592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109049 q = 1) (hb : d125748 q = 1) : d126593 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109049, d126593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109049, d126593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27467 (p : Pattern) (ha : d109055 p = 1) (hb : d125748 p = 1) : d126599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11939 q = 1) (hb : d125748 q = 1) : d126484 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11939, d126484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11939, d126484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27443 q ha hb
  have h2 (q : Pattern) (ha : d11940 q = 1) (hb : d125748 q = 1) : d126485 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11940, d126485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11940, d126485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d11949 q = 1) (hb : d125748 q = 1) : d126493 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d126493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27443 q ha hb
    | true =>
      simp only [d11949, d126493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27445 q ha hb
  have h4 (q : Pattern) (ha : d11950 q = 1) (hb : d125748 q = 1) : d126494 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d126494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11950, d126494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11951 q = 1) (hb : d125748 q = 1) : d126495 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11951, d126495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11951, d126495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109033 q = 1) (hb : d125748 q = 1) : d126549 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109033, d126549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27453 q ha hb
    | true =>
      simp only [d109033, d126549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27458 q ha hb
  have h7 (q : Pattern) (ha : d12062 q = 1) (hb : d125748 q = 1) : d12062 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12063 q = 1) (hb : d125748 q = 1) : d126551 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12063, d126551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27446 q ha hb
    | true =>
      simp only [d12063, d126551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109034 q = 1) (hb : d125748 q = 1) : d126552 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109034, d126552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109034, d126552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109035 q = 1) (hb : d125748 q = 1) : d126553 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109035, d126553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109035, d126553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d109036 q = 1) (hb : d125748 q = 1) : d126554 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109036, d126554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109036, d126554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d109040 q = 1) (hb : d125748 q = 1) : d126558 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109040, d126558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109040, d126558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27459 q ha hb
  have h13 (q : Pattern) (ha : d12072 q = 1) (hb : d125748 q = 1) : d12072 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d109041 q = 1) (hb : d125748 q = 1) : d126559 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109041, d126559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109041, d126559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109042 q = 1) (hb : d125748 q = 1) : d126560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109042, d126560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d109042, d126560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d109043 q = 1) (hb : d125748 q = 1) : d126561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109043, d126561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109043, d126561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d109044 q = 1) (hb : d125748 q = 1) : d126562 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109044, d126562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109044, d126562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d109050 q = 1) (hb : d125748 q = 1) : d126594 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109050, d126594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109050, d126594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27466 q ha hb
  have h19 (q : Pattern) (ha : d12165 q = 1) (hb : d125748 q = 1) : d12165 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d109051 q = 1) (hb : d125748 q = 1) : d126595 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109051, d126595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109051, d126595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d109052 q = 1) (hb : d125748 q = 1) : d126596 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109052, d126596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d109052, d126596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d109053 q = 1) (hb : d125748 q = 1) : d126597 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109053, d126597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109053, d126597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d109054 q = 1) (hb : d125748 q = 1) : d126598 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109054, d126598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d109054, d126598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d109055 q = 1) (hb : d125748 q = 1) : d126599 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109055, d126599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109055, d126599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro27468 (p : Pattern) (ha : d109061 p = 1) (hb : d125748 p = 1) : d126605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109056 q = 1) (hb : d125748 q = 1) : d126600 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109056, d126600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109056, d126600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27467 q ha hb
  have h2 (q : Pattern) (ha : d109057 q = 1) (hb : d125748 q = 1) : d126601 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109057, d126601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109057, d126601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109058 q = 1) (hb : d125748 q = 1) : d126602 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109058, d126602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109058, d126602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109059 q = 1) (hb : d125748 q = 1) : d126603 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109059, d126603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109059, d126603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109060 q = 1) (hb : d125748 q = 1) : d126604 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109060, d126604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109060, d126604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109061 q = 1) (hb : d125748 q = 1) : d126605 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109061, d126605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109061, d126605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27469 (p : Pattern) (ha : d109067 p = 1) (hb : d125748 p = 1) : d126611 p = 1 := by
  have h0 (q : Pattern) (ha : d108896 q = 1) (hb : d125748 q = 1) : d126048 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108896, d126048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27330 q ha hb
    | true =>
      simp only [d108896, d126048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27356 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108936 q = 1) (hb : d125748 q = 1) : d126186 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108936, d126186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108936, d126186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27384 q ha hb
  have h3 (q : Pattern) (ha : d108937 q = 1) (hb : d125748 q = 1) : d126187 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108937, d126187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108937, d126187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108977 q = 1) (hb : d125748 q = 1) : d126325 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108977, d126325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108977, d126325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27412 q ha hb
  have h5 (q : Pattern) (ha : d108978 q = 1) (hb : d125748 q = 1) : d126326 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108978, d126326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108978, d126326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108979 q = 1) (hb : d125748 q = 1) : d126327 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108979, d126327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108979, d126327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109019 q = 1) (hb : d125748 q = 1) : d126465 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109019, d126465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109019, d126465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27440 q ha hb
  have h8 (q : Pattern) (ha : d109020 q = 1) (hb : d125748 q = 1) : d126466 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109020, d126466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109020, d126466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109021 q = 1) (hb : d125748 q = 1) : d126467 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109021, d126467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109021, d126467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109022 q = 1) (hb : d125748 q = 1) : d126468 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109022, d126468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109022, d126468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109062 q = 1) (hb : d125748 q = 1) : d126606 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109062, d126606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109062, d126606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27468 q ha hb
  have h12 (q : Pattern) (ha : d109063 q = 1) (hb : d125748 q = 1) : d126607 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109063, d126607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109063, d126607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109064 q = 1) (hb : d125748 q = 1) : d126608 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109064, d126608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109064, d126608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109065 q = 1) (hb : d125748 q = 1) : d126609 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109065, d126609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109065, d126609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109066 q = 1) (hb : d125748 q = 1) : d126610 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109066, d126610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109066, d126610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109067 q = 1) (hb : d125748 q = 1) : d126611 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109067, d126611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109067, d126611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro27470 (p : Pattern) (ha : d109073 p = 1) (hb : d125748 p = 1) : d126617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109068 q = 1) (hb : d125748 q = 1) : d126612 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109068, d126612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27469 q ha hb
    | true =>
      simp only [d109068, d126612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109069 q = 1) (hb : d125748 q = 1) : d126613 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109069, d126613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109069, d126613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109070 q = 1) (hb : d125748 q = 1) : d126614 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109070, d126614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109070, d126614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109071 q = 1) (hb : d125748 q = 1) : d126615 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109071, d126615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109071, d126615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109072 q = 1) (hb : d125748 q = 1) : d126616 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109072, d126616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109072, d126616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109073 q = 1) (hb : d125748 q = 1) : d126617 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109073, d126617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109073, d126617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27471 (p : Pattern) (ha : d109079 p = 1) (hb : d125748 p = 1) : d126623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109074 q = 1) (hb : d125748 q = 1) : d126618 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109074, d126618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27470 q ha hb
    | true =>
      simp only [d109074, d126618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109075 q = 1) (hb : d125748 q = 1) : d126619 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109075, d126619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109075, d126619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109076 q = 1) (hb : d125748 q = 1) : d126620 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109076, d126620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109076, d126620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109077 q = 1) (hb : d125748 q = 1) : d126621 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109077, d126621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109077, d126621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109078 q = 1) (hb : d125748 q = 1) : d126622 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109078, d126622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109078, d126622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109079 q = 1) (hb : d125748 q = 1) : d126623 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109079, d126623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109079, d126623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27472 (p : Pattern) (ha : d109085 p = 1) (hb : d125748 p = 1) : d126629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109080 q = 1) (hb : d125748 q = 1) : d126624 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109080, d126624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27471 q ha hb
    | true =>
      simp only [d109080, d126624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109081 q = 1) (hb : d125748 q = 1) : d126625 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109081, d126625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109081, d126625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109082 q = 1) (hb : d125748 q = 1) : d126626 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109082, d126626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109082, d126626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109083 q = 1) (hb : d125748 q = 1) : d126627 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109083, d126627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109083, d126627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109084 q = 1) (hb : d125748 q = 1) : d126628 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109084, d126628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109084, d126628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109085 q = 1) (hb : d125748 q = 1) : d126629 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109085, d126629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109085, d126629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27473 (p : Pattern) (ha : d109091 p = 1) (hb : d125748 p = 1) : d126635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109086 q = 1) (hb : d125748 q = 1) : d126630 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109086, d126630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27472 q ha hb
    | true =>
      simp only [d109086, d126630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109087 q = 1) (hb : d125748 q = 1) : d126631 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109087, d126631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109087, d126631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109088 q = 1) (hb : d125748 q = 1) : d126632 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d126632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109088, d126632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109089 q = 1) (hb : d125748 q = 1) : d126633 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d126633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109089, d126633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109090 q = 1) (hb : d125748 q = 1) : d126634 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, d126634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, d126634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109091 q = 1) (hb : d125748 q = 1) : d126635 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, d126635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109091, d126635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27474 (p : Pattern) (ha : d109097 p = 1) (hb : d125748 p = 1) : d126641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109092 q = 1) (hb : d125748 q = 1) : d126636 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, d126636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27473 q ha hb
    | true =>
      simp only [d109092, d126636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109093 q = 1) (hb : d125748 q = 1) : d126637 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, d126637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, d126637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109094 q = 1) (hb : d125748 q = 1) : d126638 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, d126638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, d126638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109095 q = 1) (hb : d125748 q = 1) : d126639 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, d126639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, d126639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109096 q = 1) (hb : d125748 q = 1) : d126640 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, d126640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, d126640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109097 q = 1) (hb : d125748 q = 1) : d126641 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, d126641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, d126641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27475 (p : Pattern) (ha : d109103 p = 1) (hb : d125748 p = 1) : d126647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109098 q = 1) (hb : d125748 q = 1) : d126642 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, d126642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27474 q ha hb
    | true =>
      simp only [d109098, d126642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109099 q = 1) (hb : d125748 q = 1) : d126643 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, d126643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, d126643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109100 q = 1) (hb : d125748 q = 1) : d126644 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, d126644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, d126644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109101 q = 1) (hb : d125748 q = 1) : d126645 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, d126645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, d126645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109102 q = 1) (hb : d125748 q = 1) : d126646 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, d126646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, d126646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109103 q = 1) (hb : d125748 q = 1) : d126647 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, d126647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, d126647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27476 (p : Pattern) (ha : d109109 p = 1) (hb : d125748 p = 1) : d126653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d125748 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109104 q = 1) (hb : d125748 q = 1) : d126648 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, d126648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27475 q ha hb
    | true =>
      simp only [d109104, d126648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109105 q = 1) (hb : d125748 q = 1) : d126649 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, d126649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, d126649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109106 q = 1) (hb : d125748 q = 1) : d126650 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, d126650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, d126650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109107 q = 1) (hb : d125748 q = 1) : d126651 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, d126651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, d126651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109108 q = 1) (hb : d125748 q = 1) : d126652 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, d126652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, d126652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109109 q = 1) (hb : d125748 q = 1) : d126653 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, d126653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, d126653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro27477 (p : Pattern) (ha : d81527 p = 1) (hb : d125750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10649 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10650 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10651 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10863 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10863, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d81526 q = 1) (hb : d125749 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81526, d125749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d81526, d125749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d81527 q = 1) (hb : d125750 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81527, d125750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81527, d125750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro27478 (p : Pattern) (ha : d92321 p = 1) (hb : d125756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d125751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27477 q ha hb
    | true =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d125752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d125753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d125754 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92320 q = 1) (hb : d125755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92320, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92320, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92321 q = 1) (hb : d125756 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92321, d125756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92321, d125756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27479 (p : Pattern) (ha : d92327 p = 1) (hb : d125762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d92322 q = 1) (hb : d125757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27478 q ha hb
    | true =>
      simp only [d92322, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92323 q = 1) (hb : d125758 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92323, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92323, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92324 q = 1) (hb : d125759 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92324, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92324, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92325 q = 1) (hb : d125760 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92325, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d92325, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92326 q = 1) (hb : d125761 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92326, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92326, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92327 q = 1) (hb : d125762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92327, d125762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92327, d125762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro27480 (p : Pattern) (ha : d92328 p = 1) (hb : d125763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d125751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27477 q ha hb
    | true =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d125752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d125753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d125754 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92320 q = 1) (hb : d125755 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92320, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92320, d125755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92328 q = 1) (hb : d125763 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92328, d125763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92328, d125763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro27481 (p : Pattern) (ha : d92334 p = 1) (hb : d125769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d92322 q = 1) (hb : d125757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27478 q ha hb
    | true =>
      simp only [d92322, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92323 q = 1) (hb : d125758 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92323, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92323, d125758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d92324 q = 1) (hb : d125759 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92324, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92324, d125759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92325 q = 1) (hb : d125760 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92325, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d92325, d125760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92326 q = 1) (hb : d125761 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92326, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92326, d125761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d92329 q = 1) (hb : d125764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27480 q ha hb
    | true =>
      simp only [d92329, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92330 q = 1) (hb : d125765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92330, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92330, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d92331 q = 1) (hb : d125766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92331, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92331, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92332 q = 1) (hb : d125767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92332, d125767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d92332, d125767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92333 q = 1) (hb : d125768 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92333, d125768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d92333, d125768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92334 q = 1) (hb : d125769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92334, d125769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92334, d125769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro27482 (p : Pattern) (ha : d92341 p = 1) (hb : d125776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92329 q = 1) (hb : d125764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27480 q ha hb
    | true =>
      simp only [d92329, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92330 q = 1) (hb : d125765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92330, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92330, d125765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92331 q = 1) (hb : d125766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92331, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92331, d125766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92339 q = 1) (hb : d125774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92339, d125774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92339, d125774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92340 q = 1) (hb : d125775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92340, d125775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92340, d125775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92341 q = 1) (hb : d125776 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92341, d125776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92341, d125776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27483 (p : Pattern) (ha : d81560 p = 1) (hb : d125783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10686 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10687 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10688 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11021 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11021, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d81559 q = 1) (hb : d125782 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81559, d125782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d81559, d125782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d81560 q = 1) (hb : d125783 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81560, d125783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d81560, d125783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro27484 (p : Pattern) (ha : d92350 p = 1) (hb : d125789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81561 q = 1) (hb : d125784 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81561, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27483 q ha hb
    | true =>
      simp only [d81561, d125784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81562 q = 1) (hb : d125785 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81562, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81562, d125785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92347 q = 1) (hb : d125786 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92347, d125786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92347, d125786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92348 q = 1) (hb : d125787 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92348, d125787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92348, d125787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92349 q = 1) (hb : d125788 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92349, d125788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92349, d125788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92350 q = 1) (hb : d125789 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92350, d125789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92350, d125789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro27485 (p : Pattern) (ha : d92356 p = 1) (hb : d125795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92351 q = 1) (hb : d125790 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92351, d125790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27484 q ha hb
    | true =>
      simp only [d92351, d125790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92352 q = 1) (hb : d125791 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92352, d125791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92352, d125791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d92353 q = 1) (hb : d125792 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92353, d125792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92353, d125792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92354 q = 1) (hb : d125793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92354, d125793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92354, d125793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92355 q = 1) (hb : d125794 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92355, d125794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92355, d125794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92356 q = 1) (hb : d125795 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92356, d125795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92356, d125795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro27486 (p : Pattern) (ha : d92362 p = 1) (hb : d125801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92335 q = 1) (hb : d125770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92335, d125770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27479 q ha hb
    | true =>
      simp only [d92335, d125770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27481 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d92336 q = 1) (hb : d125771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92336, d125771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92336, d125771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d92337 q = 1) (hb : d125772 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92337, d125772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92337, d125772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92338 q = 1) (hb : d125773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92338, d125773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d92338, d125773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92342 q = 1) (hb : d125777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92342, d125777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92342, d125777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27482 q ha hb
  have h12 (q : Pattern) (ha : d92343 q = 1) (hb : d125778 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92343, d125778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92343, d125778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92344 q = 1) (hb : d125779 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92344, d125779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92344, d125779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92345 q = 1) (hb : d125780 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92345, d125780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92345, d125780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92346 q = 1) (hb : d125781 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92346, d125781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92346, d125781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92357 q = 1) (hb : d125796 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92357, d125796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92357, d125796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27485 q ha hb
  have h17 (q : Pattern) (ha : d92358 q = 1) (hb : d125797 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92358, d125797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92358, d125797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d92359 q = 1) (hb : d125798 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92359, d125798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92359, d125798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92360 q = 1) (hb : d125799 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92360, d125799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d92360, d125799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d92361 q = 1) (hb : d125800 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92361, d125800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92361, d125800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92362 q = 1) (hb : d125801 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92362, d125801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92362, d125801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro27487 (p : Pattern) (ha : d92372 p = 1) (hb : d125811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d125757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27478 q ha hb
    | true =>
      simp only [d92322, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d125807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d125808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d125809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d125810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92372 q = 1) (hb : d125811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92372, d125811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92372, d125811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27488 (p : Pattern) (ha : d92379 p = 1) (hb : d125818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d125757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27478 q ha hb
    | true =>
      simp only [d92322, d125757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d125807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d125807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d125808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d125808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d125809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d125809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d125810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d125810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92329 q = 1) (hb : d125764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27480 q ha hb
    | true =>
      simp only [d92329, d125764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d92375 q = 1) (hb : d125814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92375, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92375, d125814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92376 q = 1) (hb : d125815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92376, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92376, d125815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92377 q = 1) (hb : d125816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92377, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92377, d125816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92378 q = 1) (hb : d125817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92378, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92378, d125817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92379 q = 1) (hb : d125818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92379, d125818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92379, d125818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro27489 (p : Pattern) (ha : d92384 p = 1) (hb : d125823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d125751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27477 q ha hb
    | true =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d125752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d125753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d125754 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92383 q = 1) (hb : d125822 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92383, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92383, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92384 q = 1) (hb : d125823 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92384, d125823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92384, d125823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27490 (p : Pattern) (ha : d92391 p = 1) (hb : d125830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d125751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27477 q ha hb
    | true =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d125752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d125753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92389 q = 1) (hb : d125828 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92389, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92389, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92390 q = 1) (hb : d125829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92390, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92390, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92391 q = 1) (hb : d125830 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92391, d125830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92391, d125830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27491 (p : Pattern) (ha : d92396 p = 1) (hb : d125836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10742 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10743 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10744 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d81585 q = 1) (hb : d125834 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81585, d125834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81585, d125834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d51996 q = 1) (hb : d88338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d51996, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q hb ha
    | true =>
      simp only [d51996, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d51997 q = 1) (hb : d88339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d51997, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51997, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51998 q = 1) (hb : d88340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d51998, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51998, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52222 q = 1) (hb : d88341 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52222, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52222, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d92395 q = 1) (hb : d125835 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92395, d125835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92395, d125835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92396 q = 1) (hb : d125836 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92396, d125836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92396, d125836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro27492 (p : Pattern) (ha : d92402 p = 1) (hb : d125842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d125837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27491 q ha hb
    | true =>
      simp only [d92397, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d125838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81528 q = 1) (hb : d125751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27477 q ha hb
    | true =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81529 q = 1) (hb : d125752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92399 q = 1) (hb : d125839 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92399, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92399, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92400 q = 1) (hb : d125840 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92400, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92400, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92401 q = 1) (hb : d125841 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92401, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92401, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92402 q = 1) (hb : d125842 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92402, d125842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92402, d125842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro27493 (p : Pattern) (ha : d92408 p = 1) (hb : d125848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d125751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27477 q ha hb
    | true =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d125752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92405 q = 1) (hb : d125845 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92405, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92405, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92406 q = 1) (hb : d125846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92406, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92406, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92407 q = 1) (hb : d125847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92407, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92407, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92408 q = 1) (hb : d125848 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92408, d125848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92408, d125848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro27494 (p : Pattern) (ha : d92414 p = 1) (hb : d125854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92385 q = 1) (hb : d125824 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92385, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27489 q ha hb
    | true =>
      simp only [d92385, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d92386 q = 1) (hb : d125825 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92386, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92386, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92387 q = 1) (hb : d125826 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92387, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92387, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92388 q = 1) (hb : d125827 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92388, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92388, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92392 q = 1) (hb : d125831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92392, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27490 q ha hb
    | true =>
      simp only [d92392, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d92393 q = 1) (hb : d125832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92393, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92393, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92394 q = 1) (hb : d125833 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92394, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92394, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92403 q = 1) (hb : d125843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92403, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27492 q ha hb
    | true =>
      simp only [d92403, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27478 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92404 q = 1) (hb : d125844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92404, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92409 q = 1) (hb : d125849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92409, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27493 q ha hb
    | true =>
      simp only [d92409, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92410 q = 1) (hb : d125850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92410, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92410, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92411 q = 1) (hb : d125851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92411, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92412 q = 1) (hb : d125852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92412, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92413 q = 1) (hb : d125853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92413, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92414 q = 1) (hb : d125854 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92414, d125854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92414, d125854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro27495 (p : Pattern) (ha : d92415 p = 1) (hb : d125855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d125751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27477 q ha hb
    | true =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d125752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d125753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d125754 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d125754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92383 q = 1) (hb : d125822 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92383, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92383, d125822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92415 q = 1) (hb : d125855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92415, d125855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92415, d125855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro27496 (p : Pattern) (ha : d92420 p = 1) (hb : d125860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d125751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27477 q ha hb
    | true =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d125752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d125753 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d125753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92389 q = 1) (hb : d125828 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92389, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92389, d125828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92390 q = 1) (hb : d125829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92390, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92390, d125829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92420 q = 1) (hb : d125860 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92420, d125860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92420, d125860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro27497 (p : Pattern) (ha : d92424 p = 1) (hb : d125864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d125837 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27491 q ha hb
    | true =>
      simp only [d92397, d125837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d125838 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d125838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81528 q = 1) (hb : d125751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27477 q ha hb
    | true =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81529 q = 1) (hb : d125752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92399 q = 1) (hb : d125839 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92399, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92399, d125839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92400 q = 1) (hb : d125840 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92400, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92400, d125840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92401 q = 1) (hb : d125841 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92401, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92401, d125841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92424 q = 1) (hb : d125864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92424, d125864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92424, d125864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro27498 (p : Pattern) (ha : d92427 p = 1) (hb : d125867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d125751 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27477 q ha hb
    | true =>
      simp only [d81528, d125751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d125752 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d125752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92405 q = 1) (hb : d125845 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92405, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92405, d125845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92406 q = 1) (hb : d125846 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92406, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92406, d125846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92407 q = 1) (hb : d125847 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92407, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92407, d125847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92427 q = 1) (hb : d125867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92427, d125867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92427, d125867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro27499 (p : Pattern) (ha : d92433 p = 1) (hb : d125873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92385 q = 1) (hb : d125824 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92385, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27489 q ha hb
    | true =>
      simp only [d92385, d125824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d92386 q = 1) (hb : d125825 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92386, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92386, d125825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92387 q = 1) (hb : d125826 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92387, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92387, d125826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92388 q = 1) (hb : d125827 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92388, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92388, d125827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92392 q = 1) (hb : d125831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92392, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27490 q ha hb
    | true =>
      simp only [d92392, d125831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d92393 q = 1) (hb : d125832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92393, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92393, d125832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92394 q = 1) (hb : d125833 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92394, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92394, d125833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92403 q = 1) (hb : d125843 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92403, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27492 q ha hb
    | true =>
      simp only [d92403, d125843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27478 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92404 q = 1) (hb : d125844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92404, d125844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92409 q = 1) (hb : d125849 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92409, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27493 q ha hb
    | true =>
      simp only [d92409, d125849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92410 q = 1) (hb : d125850 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92410, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92410, d125850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92411 q = 1) (hb : d125851 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92411, d125851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92412 q = 1) (hb : d125852 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92412, d125852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92413 q = 1) (hb : d125853 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92413, d125853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92416 q = 1) (hb : d125856 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92416, d125856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27495 q ha hb
    | true =>
      simp only [d92416, d125856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d92417 q = 1) (hb : d125857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92417, d125857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92417, d125857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92418 q = 1) (hb : d125858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92418, d125858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92418, d125858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92419 q = 1) (hb : d125859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92419, d125859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92419, d125859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92421 q = 1) (hb : d125861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92421, d125861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27496 q ha hb
    | true =>
      simp only [d92421, d125861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d92422 q = 1) (hb : d125862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92422, d125862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92422, d125862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92423 q = 1) (hb : d125863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92423, d125863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92423, d125863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92425 q = 1) (hb : d125865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92425, d125865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27497 q ha hb
    | true =>
      simp only [d92425, d125865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27480 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92426 q = 1) (hb : d125866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d125866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92426, d125866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92428 q = 1) (hb : d125868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92428, d125868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27498 q ha hb
    | true =>
      simp only [d92428, d125868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d92429 q = 1) (hb : d125869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92429, d125869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d92429, d125869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92430 q = 1) (hb : d125870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d125870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92430, d125870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92431 q = 1) (hb : d125871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92431, d125871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92431, d125871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92432 q = 1) (hb : d125872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92432, d125872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92432, d125872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92433 q = 1) (hb : d125873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92433, d125873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92433, d125873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
end NetHack.Soko22Hazard87
