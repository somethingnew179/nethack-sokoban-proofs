import NetHack.Soko22Hazard87.AndIntroBlocks0122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro30750 (p : Pattern) (ha : d156346 p = 1) (hb : d157773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d156277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d156286 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156313 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156251 q = 1) (hb : d157758 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156251, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30627 q ha hb
    | true =>
      simp only [d156251, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30628 q ha hb
  have h4 (q : Pattern) (ha : d156314 q = 1) (hb : d157759 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156314, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d156314, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d156320 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d156321 q = 1) (hb : d157760 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156321, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156321, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d156322 q = 1) (hb : d157761 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156322, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156322, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156323 q = 1) (hb : d157762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156323, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156323, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d156330 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d156335 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d156338 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d156261 q = 1) (hb : d157768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156261, d157768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30630 q ha hb
    | true =>
      simp only [d156261, d157768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30631 q ha hb
  have h13 (q : Pattern) (ha : d156339 q = 1) (hb : d157769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156339, d157769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d156339, d157769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d156342 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156343 q = 1) (hb : d157770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156343, d157770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156343, d157770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d156344 q = 1) (hb : d157771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156344, d157771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d156344, d157771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156345 q = 1) (hb : d157772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156345, d157772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d156345, d157772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156346 q = 1) (hb : d157773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156346, d157773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156346, d157773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30751 (p : Pattern) (ha : d156371 p = 1) (hb : d158168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d156338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d156261 q = 1) (hb : d157768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156261, d157768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30630 q ha hb
    | true =>
      simp only [d156261, d157768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30631 q ha hb
  have h3 (q : Pattern) (ha : d156339 q = 1) (hb : d157769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156339, d157769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156339, d157769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d156342 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156343 q = 1) (hb : d157770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156343, d157770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156343, d157770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156369 q = 1) (hb : d157771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156369, d157771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156369, d157771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156370 q = 1) (hb : d157772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156370, d157772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156370, d157772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156371 q = 1) (hb : d158168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156371, d158168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156371, d158168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30752 (p : Pattern) (ha : d156452 p = 1) (hb : d158177 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d156449 q = 1) (hb : d158174 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156449, d158174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156449, d158174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156450 q = 1) (hb : d158175 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156450, d158175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156450, d158175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156451 q = 1) (hb : d158176 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156451, d158176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156451, d158176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156452 q = 1) (hb : d158177 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156452, d158177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156452, d158177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30753 (p : Pattern) (ha : d156468 p = 1) (hb : d158183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d156444 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d156457 q = 1) (hb : d158178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156457, d158178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30752 q ha hb
    | true =>
      simp only [d156457, d158178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30669 q ha hb
  have h3 (q : Pattern) (ha : d156458 q = 1) (hb : d158179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156458, d158179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156458, d158179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d156464 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156465 q = 1) (hb : d158180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156465, d158180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156465, d158180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156466 q = 1) (hb : d158181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156466, d158181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156466, d158181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156467 q = 1) (hb : d158182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156467, d158182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156467, d158182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156468 q = 1) (hb : d158183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156468, d158183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156468, d158183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30754 (p : Pattern) (ha : d156481 p = 1) (hb : d158189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d156269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156347 q = 1) (hb : d157774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156347, d157774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30749 q ha hb
    | true =>
      simp only [d156347, d157774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30750 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156365 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156366 q = 1) (hb : d157775 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156366, d157775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156366, d157775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156367 q = 1) (hb : d158166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156367, d158166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156367, d158166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156368 q = 1) (hb : d158167 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156368, d158167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156368, d158167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156372 q = 1) (hb : d158169 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156372, d158169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d156372, d158169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30751 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d156374 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d156375 q = 1) (hb : d158170 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156375, d158170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156375, d158170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d156376 q = 1) (hb : d158171 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156376, d158171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156376, d158171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d156377 q = 1) (hb : d158172 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156377, d158172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156377, d158172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d156378 q = 1) (hb : d158173 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d156378, d158173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156378, d158173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d156469 q = 1) (hb : d158184 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156469, d158184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d156469, d158184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30753 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d156476 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156477 q = 1) (hb : d158185 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156477, d158185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156477, d158185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d156478 q = 1) (hb : d158186 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156478, d158186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156478, d158186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d156479 q = 1) (hb : d158187 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156479, d158187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d156479, d158187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d156480 q = 1) (hb : d158188 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d156480, d158188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d156480, d158188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d156481 q = 1) (hb : d158189 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d156481, d158189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d156481, d158189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30755 (p : Pattern) (ha : d156487 p = 1) (hb : d158195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156482 q = 1) (hb : d158190 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d156482, d158190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156482, d158190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30754 q ha hb
  have h2 (q : Pattern) (ha : d156483 q = 1) (hb : d158191 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d156483, d158191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156483, d158191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156484 q = 1) (hb : d158192 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d156484, d158192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156484, d158192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156485 q = 1) (hb : d158193 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d156485, d158193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156485, d158193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156486 q = 1) (hb : d158194 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d156486, d158194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156486, d158194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156487 q = 1) (hb : d158195 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d156487, d158195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156487, d158195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30756 (p : Pattern) (ha : d156493 p = 1) (hb : d158201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d155304 q = 1) (hb : d158074 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d155304, d158074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30722 q ha hb
    | true =>
      simp only [d155304, d158074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30728 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155525 q = 1) (hb : d158101 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d155525, d158101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155525, d158101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30734 q ha hb
  have h3 (q : Pattern) (ha : d155526 q = 1) (hb : d158102 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d155526, d158102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d155526, d158102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155851 q = 1) (hb : d158129 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d155851, d158129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155851, d158129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30741 q ha hb
  have h5 (q : Pattern) (ha : d155852 q = 1) (hb : d158130 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d155852, d158130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155852, d158130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155853 q = 1) (hb : d158131 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d155853, d158131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155853, d158131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156188 q = 1) (hb : d158162 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d156188, d158162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156188, d158162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30748 q ha hb
  have h8 (q : Pattern) (ha : d156189 q = 1) (hb : d158163 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d156189, d158163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156189, d158163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156190 q = 1) (hb : d158164 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d156190, d158164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156190, d158164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156191 q = 1) (hb : d158165 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d156191, d158165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156191, d158165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156488 q = 1) (hb : d158196 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d156488, d158196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156488, d158196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30755 q ha hb
  have h12 (q : Pattern) (ha : d156489 q = 1) (hb : d158197 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d156489, d158197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156489, d158197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d156490 q = 1) (hb : d158198 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d156490, d158198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156490, d158198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156491 q = 1) (hb : d158199 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d156491, d158199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156491, d158199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156492 q = 1) (hb : d158200 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d156492, d158200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156492, d158200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156493 q = 1) (hb : d158201 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d156493, d158201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156493, d158201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro30757 (p : Pattern) (ha : d156499 p = 1) (hb : d158207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156494 q = 1) (hb : d158202 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d156494, d158202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30756 q ha hb
    | true =>
      simp only [d156494, d158202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156495 q = 1) (hb : d158203 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d156495, d158203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156495, d158203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156496 q = 1) (hb : d158204 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d156496, d158204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156496, d158204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156497 q = 1) (hb : d158205 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d156497, d158205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156497, d158205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156498 q = 1) (hb : d158206 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d156498, d158206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156498, d158206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156499 q = 1) (hb : d158207 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d156499, d158207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156499, d158207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30758 (p : Pattern) (ha : d156505 p = 1) (hb : d158213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156500 q = 1) (hb : d158208 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d156500, d158208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30757 q ha hb
    | true =>
      simp only [d156500, d158208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156501 q = 1) (hb : d158209 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d156501, d158209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156501, d158209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156502 q = 1) (hb : d158210 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d156502, d158210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156502, d158210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156503 q = 1) (hb : d158211 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d156503, d158211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156503, d158211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156504 q = 1) (hb : d158212 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d156504, d158212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156504, d158212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156505 q = 1) (hb : d158213 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d156505, d158213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156505, d158213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30759 (p : Pattern) (ha : d156511 p = 1) (hb : d158219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156506 q = 1) (hb : d158214 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d156506, d158214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30758 q ha hb
    | true =>
      simp only [d156506, d158214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156507 q = 1) (hb : d158215 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d156507, d158215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156507, d158215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156508 q = 1) (hb : d158216 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d156508, d158216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156508, d158216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156509 q = 1) (hb : d158217 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d156509, d158217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156509, d158217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156510 q = 1) (hb : d158218 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d156510, d158218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156510, d158218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156511 q = 1) (hb : d158219 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d156511, d158219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156511, d158219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30760 (p : Pattern) (ha : d156517 p = 1) (hb : d158225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156512 q = 1) (hb : d158220 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d156512, d158220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30759 q ha hb
    | true =>
      simp only [d156512, d158220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156513 q = 1) (hb : d158221 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d156513, d158221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156513, d158221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156514 q = 1) (hb : d158222 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d156514, d158222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156514, d158222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156515 q = 1) (hb : d158223 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d156515, d158223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156515, d158223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156516 q = 1) (hb : d158224 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d156516, d158224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156516, d158224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156517 q = 1) (hb : d158225 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d156517, d158225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156517, d158225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30761 (p : Pattern) (ha : d156523 p = 1) (hb : d158231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156518 q = 1) (hb : d158226 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d156518, d158226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30760 q ha hb
    | true =>
      simp only [d156518, d158226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156519 q = 1) (hb : d158227 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d156519, d158227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156519, d158227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156520 q = 1) (hb : d158228 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d156520, d158228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156520, d158228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156521 q = 1) (hb : d158229 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d156521, d158229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156521, d158229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156522 q = 1) (hb : d158230 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d156522, d158230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156522, d158230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156523 q = 1) (hb : d158231 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d156523, d158231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156523, d158231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30762 (p : Pattern) (ha : d156529 p = 1) (hb : d158237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156524 q = 1) (hb : d158232 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d156524, d158232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30761 q ha hb
    | true =>
      simp only [d156524, d158232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156525 q = 1) (hb : d158233 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d156525, d158233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156525, d158233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156526 q = 1) (hb : d158234 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d156526, d158234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156526, d158234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156527 q = 1) (hb : d158235 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d156527, d158235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156527, d158235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156528 q = 1) (hb : d158236 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d156528, d158236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156528, d158236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156529 q = 1) (hb : d158237 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d156529, d158237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156529, d158237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30763 (p : Pattern) (ha : d156535 p = 1) (hb : d158243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156530 q = 1) (hb : d158238 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d156530, d158238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30762 q ha hb
    | true =>
      simp only [d156530, d158238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156531 q = 1) (hb : d158239 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d156531, d158239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156531, d158239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156532 q = 1) (hb : d158240 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d156532, d158240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156532, d158240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156533 q = 1) (hb : d158241 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d156533, d158241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156533, d158241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156534 q = 1) (hb : d158242 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d156534, d158242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156534, d158242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156535 q = 1) (hb : d158243 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d156535, d158243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156535, d158243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30764 (p : Pattern) (ha : d156617 p = 1) (hb : d158248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152960 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152981 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156613 q = 1) (hb : d158244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156613, d158244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156613, d158244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d152877 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d156614 q = 1) (hb : d158245 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156614, d158245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156614, d158245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156615 q = 1) (hb : d158246 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156615, d158246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156615, d158246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156616 q = 1) (hb : d158247 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156616, d158247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156616, d158247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156617 q = 1) (hb : d158248 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156617, d158248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156617, d158248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30765 (p : Pattern) (ha : d156624 p = 1) (hb : d158253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152954 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152960 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d156613 q = 1) (hb : d158244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156613, d158244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156613, d158244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d152877 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d156614 q = 1) (hb : d158245 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156614, d158245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156614, d158245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156615 q = 1) (hb : d158246 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156615, d158246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156615, d158246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156616 q = 1) (hb : d158247 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156616, d158247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156616, d158247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d153012 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d153016 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d153018 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d156620 q = 1) (hb : d158249 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156620, d158249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156620, d158249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d152884 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156621 q = 1) (hb : d158250 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156621, d158250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156621, d158250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156622 q = 1) (hb : d158251 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156622, d158251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156622, d158251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156623 q = 1) (hb : d158252 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156623, d158252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156623, d158252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156624 q = 1) (hb : d158253 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156624, d158253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156624, d158253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30766 (p : Pattern) (ha : d156818 p = 1) (hb : d158260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153018 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156620 q = 1) (hb : d158249 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156620, d158249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156620, d158249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152884 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156621 q = 1) (hb : d158250 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156621, d158250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156621, d158250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156622 q = 1) (hb : d158258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156622, d158258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156622, d158258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156623 q = 1) (hb : d158259 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156623, d158259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156623, d158259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156818 q = 1) (hb : d158260 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156818, d158260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156818, d158260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30767 (p : Pattern) (ha : d156859 p = 1) (hb : d158270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153058 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156855 q = 1) (hb : d158266 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156855, d158266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156855, d158266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152918 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156856 q = 1) (hb : d158267 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156856, d158267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156856, d158267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156857 q = 1) (hb : d158268 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156857, d158268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156857, d158268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156858 q = 1) (hb : d158269 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156858, d158269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156858, d158269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156859 q = 1) (hb : d158270 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156859, d158270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156859, d158270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30768 (p : Pattern) (ha : d158042 p = 1) (hb : d158276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152948 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156625 q = 1) (hb : d158254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156625, d158254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30764 q ha hb
    | true =>
      simp only [d156625, d158254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30765 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153028 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156626 q = 1) (hb : d158255 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156626, d158255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156626, d158255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158032 q = 1) (hb : d158256 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158032, d158256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158032, d158256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158033 q = 1) (hb : d158257 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158033, d158257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158033, d158257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156819 q = 1) (hb : d158261 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156819, d158261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156819, d158261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30766 q ha hb
  have h8 (q : Pattern) (ha : d158034 q = 1) (hb : d158262 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158034, d158262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158034, d158262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d158035 q = 1) (hb : d158263 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158035, d158263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d158035, d158263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d158036 q = 1) (hb : d158264 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158036, d158264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158036, d158264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158037 q = 1) (hb : d158265 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158037, d158265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158037, d158265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d156860 q = 1) (hb : d158271 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156860, d158271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156860, d158271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30767 q ha hb
  have h13 (q : Pattern) (ha : d158038 q = 1) (hb : d158272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158038, d158272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158038, d158272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d158039 q = 1) (hb : d158273 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158039, d158273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158039, d158273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d158040 q = 1) (hb : d158274 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158040, d158274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d158040, d158274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d158041 q = 1) (hb : d158275 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158041, d158275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158041, d158275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158042 q = 1) (hb : d158276 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158042, d158276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d158042, d158276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro30769 (p : Pattern) (ha : d158048 p = 1) (hb : d158282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152933 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d158043 q = 1) (hb : d158277 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158043, d158277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158043, d158277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30768 q ha hb
  have h3 (q : Pattern) (ha : d158044 q = 1) (hb : d158278 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158044, d158278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158044, d158278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158045 q = 1) (hb : d158279 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158045, d158279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158045, d158279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158046 q = 1) (hb : d158280 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158046, d158280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158046, d158280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158047 q = 1) (hb : d158281 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158047, d158281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158047, d158281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158048 q = 1) (hb : d158282 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158048, d158282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158048, d158282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30770 (p : Pattern) (ha : d156735 p = 1) (hb : d158287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153115 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d153149 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156731 q = 1) (hb : d158283 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156731, d158283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156731, d158283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d153177 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d156732 q = 1) (hb : d158284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156732, d158284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156732, d158284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156733 q = 1) (hb : d158285 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156733, d158285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156733, d158285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156734 q = 1) (hb : d158286 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156734, d158286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156734, d158286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156735 q = 1) (hb : d158287 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156735, d158287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156735, d158287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30771 (p : Pattern) (ha : d156742 p = 1) (hb : d158292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d153115 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d156731 q = 1) (hb : d158283 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156731, d158283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156731, d158283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d153177 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d156732 q = 1) (hb : d158284 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156732, d158284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156732, d158284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156733 q = 1) (hb : d158285 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156733, d158285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156733, d158285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156734 q = 1) (hb : d158286 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156734, d158286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156734, d158286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d153186 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d153190 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d153192 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d156675 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d156738 q = 1) (hb : d158288 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156738, d158288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156738, d158288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d153198 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156739 q = 1) (hb : d158289 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156739, d158289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156739, d158289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156740 q = 1) (hb : d158290 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156740, d158290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156740, d158290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156741 q = 1) (hb : d158291 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156741, d158291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156741, d158291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156742 q = 1) (hb : d158292 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156742, d158292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156742, d158292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30772 (p : Pattern) (ha : d158051 p = 1) (hb : d158299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153192 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156675 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156738 q = 1) (hb : d158288 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156738, d158288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156738, d158288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d153198 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156739 q = 1) (hb : d158289 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156739, d158289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156739, d158289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156740 q = 1) (hb : d158297 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156740, d158297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156740, d158297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156741 q = 1) (hb : d158298 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156741, d158298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156741, d158298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158051 q = 1) (hb : d158299 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158051, d158299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158051, d158299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30773 (p : Pattern) (ha : d158061 p = 1) (hb : d158309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153242 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d158057 q = 1) (hb : d158305 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158057, d158305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158057, d158305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d153268 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158058 q = 1) (hb : d158306 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158058, d158306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158058, d158306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158059 q = 1) (hb : d158307 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158059, d158307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158059, d158307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158060 q = 1) (hb : d158308 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158060, d158308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158060, d158308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158061 q = 1) (hb : d158309 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158061, d158309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158061, d158309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30774 (p : Pattern) (ha : d158067 p = 1) (hb : d158315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d153109 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156743 q = 1) (hb : d158293 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156743, d158293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30770 q ha hb
    | true =>
      simp only [d156743, d158293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30771 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153205 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156744 q = 1) (hb : d158294 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156744, d158294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156744, d158294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158049 q = 1) (hb : d158295 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158049, d158295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158049, d158295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158050 q = 1) (hb : d158296 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158050, d158296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158050, d158296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158052 q = 1) (hb : d158300 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158052, d158300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158052, d158300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30772 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d153214 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d158053 q = 1) (hb : d158301 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158053, d158301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158053, d158301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d158054 q = 1) (hb : d158302 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158054, d158302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158054, d158302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158055 q = 1) (hb : d158303 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158055, d158303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d158055, d158303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d158056 q = 1) (hb : d158304 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158056, d158304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158056, d158304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d158062 q = 1) (hb : d158310 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158062, d158310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158062, d158310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30773 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d153279 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d158063 q = 1) (hb : d158311 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158063, d158311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158063, d158311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d158064 q = 1) (hb : d158312 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158064, d158312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158064, d158312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158065 q = 1) (hb : d158313 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158065, d158313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d158065, d158313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d158066 q = 1) (hb : d158314 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158066, d158314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d158066, d158314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d158067 q = 1) (hb : d158315 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158067, d158315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158067, d158315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30775 (p : Pattern) (ha : d158073 p = 1) (hb : d158321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158068 q = 1) (hb : d158316 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158068, d158316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158068, d158316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30774 q ha hb
  have h2 (q : Pattern) (ha : d158069 q = 1) (hb : d158317 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158069, d158317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158069, d158317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d158070 q = 1) (hb : d158318 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158070, d158318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158070, d158318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158071 q = 1) (hb : d158319 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158071, d158319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158071, d158319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158072 q = 1) (hb : d158320 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158072, d158320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158072, d158320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158073 q = 1) (hb : d158321 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158073, d158321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158073, d158321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30776 (p : Pattern) (ha : d156904 p = 1) (hb : d158327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d153376 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d156899 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156900 q = 1) (hb : d158323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156900, d158323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156900, d158323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d153420 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d156901 q = 1) (hb : d158324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156901, d158324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156901, d158324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156902 q = 1) (hb : d158325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156902, d158325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156902, d158325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156903 q = 1) (hb : d158326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156903, d158326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156903, d158326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156904 q = 1) (hb : d158327 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156904, d158327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156904, d158327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30777 (p : Pattern) (ha : d156914 p = 1) (hb : d158332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d153335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153344 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d156899 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d156900 q = 1) (hb : d158323 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156900, d158323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156900, d158323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d153420 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d156901 q = 1) (hb : d158324 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156901, d158324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156901, d158324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156902 q = 1) (hb : d158325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156902, d158325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156902, d158325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156903 q = 1) (hb : d158326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156903, d158326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156903, d158326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d153430 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d153435 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d153437 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d156909 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d156910 q = 1) (hb : d158328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156910, d158328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156910, d158328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d153444 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156911 q = 1) (hb : d158329 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156911, d158329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156911, d158329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156912 q = 1) (hb : d158330 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156912, d158330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156912, d158330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156913 q = 1) (hb : d158331 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156913, d158331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156913, d158331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156914 q = 1) (hb : d158332 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156914, d158332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156914, d158332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30778 (p : Pattern) (ha : d158077 p = 1) (hb : d158339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156909 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156910 q = 1) (hb : d158328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156910, d158328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156910, d158328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d153444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156911 q = 1) (hb : d158329 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156911, d158329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156911, d158329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156912 q = 1) (hb : d158337 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156912, d158337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156912, d158337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156913 q = 1) (hb : d158338 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156913, d158338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156913, d158338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158077 q = 1) (hb : d158339 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158077, d158339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158077, d158339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30779 (p : Pattern) (ha : d158088 p = 1) (hb : d158349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153516 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d158083 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d158084 q = 1) (hb : d158345 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158084, d158345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158084, d158345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d153556 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158085 q = 1) (hb : d158346 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158085, d158346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158085, d158346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158086 q = 1) (hb : d158347 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158086, d158347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158086, d158347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158087 q = 1) (hb : d158348 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158087, d158348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158087, d158348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158088 q = 1) (hb : d158349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158088, d158349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158088, d158349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30780 (p : Pattern) (ha : d158094 p = 1) (hb : d158355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d153327 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156915 q = 1) (hb : d158333 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156915, d158333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30776 q ha hb
    | true =>
      simp only [d156915, d158333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30777 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153462 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156916 q = 1) (hb : d158334 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156916, d158334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156916, d158334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158075 q = 1) (hb : d158335 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158075, d158335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158075, d158335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158076 q = 1) (hb : d158336 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158076, d158336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158076, d158336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158078 q = 1) (hb : d158340 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158078, d158340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158078, d158340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30778 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d153471 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d158079 q = 1) (hb : d158341 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158079, d158341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158079, d158341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d158080 q = 1) (hb : d158342 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158080, d158342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158080, d158342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158081 q = 1) (hb : d158343 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158081, d158343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d158081, d158343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d158082 q = 1) (hb : d158344 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158082, d158344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158082, d158344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d158089 q = 1) (hb : d158350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158089, d158350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158089, d158350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30779 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d153572 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d158090 q = 1) (hb : d158351 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158090, d158351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158090, d158351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d158091 q = 1) (hb : d158352 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158091, d158352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158091, d158352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158092 q = 1) (hb : d158353 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158092, d158353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d158092, d158353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d158093 q = 1) (hb : d158354 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158093, d158354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d158093, d158354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d158094 q = 1) (hb : d158355 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158094, d158355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158094, d158355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30781 (p : Pattern) (ha : d158100 p = 1) (hb : d158361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158095 q = 1) (hb : d158356 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158095, d158356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158095, d158356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30780 q ha hb
  have h2 (q : Pattern) (ha : d158096 q = 1) (hb : d158357 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158096, d158357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158096, d158357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d158097 q = 1) (hb : d158358 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158097, d158358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158097, d158358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158098 q = 1) (hb : d158359 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158098, d158359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158098, d158359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158099 q = 1) (hb : d158360 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158099, d158360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158099, d158360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158100 q = 1) (hb : d158361 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158100, d158361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158100, d158361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30782 (p : Pattern) (ha : d157162 p = 1) (hb : d158368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153672 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153681 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d153723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d157157 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d157158 q = 1) (hb : d158364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157158, d158364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d157158, d158364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d153798 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d157159 q = 1) (hb : d158365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157159, d158365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d157159, d158365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d157160 q = 1) (hb : d158366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157160, d158366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d157160, d158366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d157161 q = 1) (hb : d158367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157161, d158367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157161, d158367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d157162 q = 1) (hb : d158368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d157162, d158368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157162, d158368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30783 (p : Pattern) (ha : d157172 p = 1) (hb : d158373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d153672 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153681 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153723 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d157157 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157158 q = 1) (hb : d158364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157158, d158364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d157158, d158364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d153798 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d157159 q = 1) (hb : d158365 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157159, d158365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d157159, d158365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d157160 q = 1) (hb : d158366 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157160, d158366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157160, d158366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d157161 q = 1) (hb : d158367 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157161, d158367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157161, d158367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d153808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d153813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d153816 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d157167 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d157168 q = 1) (hb : d158369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157168, d158369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d157168, d158369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d153823 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d157169 q = 1) (hb : d158370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157169, d158370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d157169, d158370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d157170 q = 1) (hb : d158371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157170, d158371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d157170, d158371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d157171 q = 1) (hb : d158372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157171, d158372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d157171, d158372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d157172 q = 1) (hb : d158373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d157172, d158373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d157172, d158373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30784 (p : Pattern) (ha : d158105 p = 1) (hb : d158380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153816 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157167 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157168 q = 1) (hb : d158369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157168, d158369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157168, d158369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d153823 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d157169 q = 1) (hb : d158370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157169, d158370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d157169, d158370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d157170 q = 1) (hb : d158378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157170, d158378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157170, d158378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d157171 q = 1) (hb : d158379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157171, d158379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157171, d158379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158105 q = 1) (hb : d158380 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158105, d158380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158105, d158380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30785 (p : Pattern) (ha : d158116 p = 1) (hb : d158390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153937 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d158111 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d158112 q = 1) (hb : d158386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158112, d158386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158112, d158386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d154006 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158113 q = 1) (hb : d158387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158113, d158387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158113, d158387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158114 q = 1) (hb : d158388 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158114, d158388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158114, d158388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158115 q = 1) (hb : d158389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158115, d158389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158115, d158389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158116 q = 1) (hb : d158390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158116, d158390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158116, d158390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30786 (p : Pattern) (ha : d158122 p = 1) (hb : d158396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d153664 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157173 q = 1) (hb : d158374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d157173, d158374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30782 q ha hb
    | true =>
      simp only [d157173, d158374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30783 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153846 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157174 q = 1) (hb : d158375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d157174, d158375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157174, d158375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158103 q = 1) (hb : d158376 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158103, d158376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158103, d158376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158104 q = 1) (hb : d158377 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158104, d158377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158104, d158377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158106 q = 1) (hb : d158381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158106, d158381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158106, d158381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30784 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d153855 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d158107 q = 1) (hb : d158382 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158107, d158382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158107, d158382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d158108 q = 1) (hb : d158383 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158108, d158383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158108, d158383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158109 q = 1) (hb : d158384 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158109, d158384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d158109, d158384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d158110 q = 1) (hb : d158385 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158110, d158385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158110, d158385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d158117 q = 1) (hb : d158391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158117, d158391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158117, d158391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30785 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d154022 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d158118 q = 1) (hb : d158392 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158118, d158392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158118, d158392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d158119 q = 1) (hb : d158393 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158119, d158393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158119, d158393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158120 q = 1) (hb : d158394 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158120, d158394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d158120, d158394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d158121 q = 1) (hb : d158395 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158121, d158395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d158121, d158395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d158122 q = 1) (hb : d158396 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158122, d158396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158122, d158396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30787 (p : Pattern) (ha : d158128 p = 1) (hb : d158402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158123 q = 1) (hb : d158397 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158123, d158397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158123, d158397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30786 q ha hb
  have h2 (q : Pattern) (ha : d158124 q = 1) (hb : d158398 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158124, d158398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158124, d158398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d158125 q = 1) (hb : d158399 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158125, d158399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158125, d158399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158126 q = 1) (hb : d158400 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158126, d158400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158126, d158400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158127 q = 1) (hb : d158401 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158127, d158401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158127, d158401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158128 q = 1) (hb : d158402 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158128, d158402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158128, d158402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30788 (p : Pattern) (ha : d157450 p = 1) (hb : d158410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d154130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d154139 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d154180 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d157445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d157446 q = 1) (hb : d158406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157446, d158406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d157446, d158406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d154255 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d157447 q = 1) (hb : d158407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157447, d158407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d157447, d158407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d157448 q = 1) (hb : d158408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157448, d158408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d157448, d158408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d157449 q = 1) (hb : d158409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157449, d158409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157449, d158409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d157450 q = 1) (hb : d158410 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d157450, d158410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157450, d158410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30789 (p : Pattern) (ha : d157460 p = 1) (hb : d158415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d154130 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d154139 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d154180 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d157445 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157446 q = 1) (hb : d158406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157446, d158406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d157446, d158406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d154255 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d157447 q = 1) (hb : d158407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157447, d158407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d157447, d158407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d157448 q = 1) (hb : d158408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157448, d158408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157448, d158408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d157449 q = 1) (hb : d158409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157449, d158409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157449, d158409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d154265 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d154270 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d154273 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d157455 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d157456 q = 1) (hb : d158411 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157456, d158411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d157456, d158411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d154280 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d157457 q = 1) (hb : d158412 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157457, d158412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d157457, d158412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d157458 q = 1) (hb : d158413 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157458, d158413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d157458, d158413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d157459 q = 1) (hb : d158414 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157459, d158414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d157459, d158414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d157460 q = 1) (hb : d158415 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d157460, d158415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d157460, d158415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30790 (p : Pattern) (ha : d158134 p = 1) (hb : d158422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d154273 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157455 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157456 q = 1) (hb : d158411 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157456, d158411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157456, d158411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d154280 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d157457 q = 1) (hb : d158412 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157457, d158412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d157457, d158412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d157458 q = 1) (hb : d158420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157458, d158420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157458, d158420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d157459 q = 1) (hb : d158421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157459, d158421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157459, d158421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158134 q = 1) (hb : d158422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158134, d158422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158134, d158422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30791 (p : Pattern) (ha : d158149 p = 1) (hb : d158432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d154398 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d158144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d158145 q = 1) (hb : d158428 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158145, d158428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158145, d158428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d154467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158146 q = 1) (hb : d158429 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158146, d158429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158146, d158429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158147 q = 1) (hb : d158430 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158147, d158430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158147, d158430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158148 q = 1) (hb : d158431 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158148, d158431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158148, d158431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158149 q = 1) (hb : d158432 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158149, d158432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158149, d158432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30792 (p : Pattern) (ha : d158155 p = 1) (hb : d158438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d154122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157461 q = 1) (hb : d158416 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d157461, d158416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30788 q ha hb
    | true =>
      simp only [d157461, d158416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30789 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d154303 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157462 q = 1) (hb : d158417 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d157462, d158417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157462, d158417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158132 q = 1) (hb : d158418 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158132, d158418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158132, d158418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158133 q = 1) (hb : d158419 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158133, d158419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158133, d158419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158135 q = 1) (hb : d158423 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158135, d158423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158135, d158423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30790 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d154312 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d158136 q = 1) (hb : d158424 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158136, d158424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158136, d158424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d158137 q = 1) (hb : d158425 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158137, d158425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158137, d158425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158138 q = 1) (hb : d158426 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158138, d158426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d158138, d158426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d158139 q = 1) (hb : d158427 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158139, d158427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158139, d158427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d158150 q = 1) (hb : d158433 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158150, d158433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158150, d158433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30791 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d154483 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d158151 q = 1) (hb : d158434 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158151, d158434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158151, d158434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d158152 q = 1) (hb : d158435 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158152, d158435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158152, d158435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158153 q = 1) (hb : d158436 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158153, d158436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d158153, d158436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d158154 q = 1) (hb : d158437 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158154, d158437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d158154, d158437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d158155 q = 1) (hb : d158438 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158155, d158438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158155, d158438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30793 (p : Pattern) (ha : d158161 p = 1) (hb : d158444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158156 q = 1) (hb : d158439 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158156, d158439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158156, d158439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30792 q ha hb
  have h2 (q : Pattern) (ha : d158157 q = 1) (hb : d158440 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158157, d158440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158157, d158440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d158158 q = 1) (hb : d158441 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158158, d158441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158158, d158441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158159 q = 1) (hb : d158442 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158159, d158442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158159, d158442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158160 q = 1) (hb : d158443 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158160, d158443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158160, d158443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158161 q = 1) (hb : d158444 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158161, d158444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158161, d158444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30794 (p : Pattern) (ha : d157763 p = 1) (hb : d158453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d154584 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d154593 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d154620 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d157758 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d157759 q = 1) (hb : d158449 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157759, d158449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d157759, d158449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d154687 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d157760 q = 1) (hb : d158450 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157760, d158450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d157760, d158450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d157761 q = 1) (hb : d158451 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157761, d158451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d157761, d158451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d157762 q = 1) (hb : d158452 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157762, d158452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157762, d158452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d157763 q = 1) (hb : d158453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d157763, d158453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157763, d158453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30795 (p : Pattern) (ha : d157773 p = 1) (hb : d158458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d154584 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d154593 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d154620 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d157758 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157759 q = 1) (hb : d158449 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157759, d158449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d157759, d158449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d154687 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d157760 q = 1) (hb : d158450 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157760, d158450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d157760, d158450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d157761 q = 1) (hb : d158451 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157761, d158451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157761, d158451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d157762 q = 1) (hb : d158452 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157762, d158452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157762, d158452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d154697 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d154702 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d154705 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d157768 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d157769 q = 1) (hb : d158454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157769, d158454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d157769, d158454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d154712 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d157770 q = 1) (hb : d158455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157770, d158455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d157770, d158455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d157771 q = 1) (hb : d158456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157771, d158456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d157771, d158456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d157772 q = 1) (hb : d158457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157772, d158457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d157772, d158457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d157773 q = 1) (hb : d158458 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d157773, d158458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d157773, d158458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30796 (p : Pattern) (ha : d158168 p = 1) (hb : d158465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d154705 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157768 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157769 q = 1) (hb : d158454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d157769, d158454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157769, d158454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d154712 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d157770 q = 1) (hb : d158455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d157770, d158455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d157770, d158455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d157771 q = 1) (hb : d158463 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d157771, d158463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157771, d158463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d157772 q = 1) (hb : d158464 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d157772, d158464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d157772, d158464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158168 q = 1) (hb : d158465 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158168, d158465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158168, d158465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30797 (p : Pattern) (ha : d158183 p = 1) (hb : d158475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d154814 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d158178 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d158179 q = 1) (hb : d158471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d158179, d158471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158179, d158471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d154877 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158180 q = 1) (hb : d158472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d158180, d158472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158180, d158472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158181 q = 1) (hb : d158473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d158181, d158473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158181, d158473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158182 q = 1) (hb : d158474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d158182, d158474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158182, d158474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d158183 q = 1) (hb : d158475 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d158183, d158475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158183, d158475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30798 (p : Pattern) (ha : d158189 p = 1) (hb : d158481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d154576 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157774 q = 1) (hb : d158459 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d157774, d158459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30794 q ha hb
    | true =>
      simp only [d157774, d158459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30795 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d154735 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157775 q = 1) (hb : d158460 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d157775, d158460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d157775, d158460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d158166 q = 1) (hb : d158461 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158166, d158461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158166, d158461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158167 q = 1) (hb : d158462 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158167, d158462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158167, d158462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158169 q = 1) (hb : d158466 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158169, d158466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158169, d158466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30796 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d154744 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d158170 q = 1) (hb : d158467 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158170, d158467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d158170, d158467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d158171 q = 1) (hb : d158468 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158171, d158468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d158171, d158468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d158172 q = 1) (hb : d158469 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158172, d158469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d158172, d158469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d158173 q = 1) (hb : d158470 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158173, d158470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158173, d158470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d158184 q = 1) (hb : d158476 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d158184, d158476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158184, d158476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30797 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d154893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d158185 q = 1) (hb : d158477 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d158185, d158477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d158185, d158477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d158186 q = 1) (hb : d158478 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d158186, d158478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158186, d158478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d158187 q = 1) (hb : d158479 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d158187, d158479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d158187, d158479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d158188 q = 1) (hb : d158480 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d158188, d158480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d158188, d158480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d158189 q = 1) (hb : d158481 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d158189, d158481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d158189, d158481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30799 (p : Pattern) (ha : d158195 p = 1) (hb : d158487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158190 q = 1) (hb : d158482 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d158190, d158482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158190, d158482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30798 q ha hb
  have h2 (q : Pattern) (ha : d158191 q = 1) (hb : d158483 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d158191, d158483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158191, d158483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d158192 q = 1) (hb : d158484 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d158192, d158484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158192, d158484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158193 q = 1) (hb : d158485 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d158193, d158485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158193, d158485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d158194 q = 1) (hb : d158486 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d158194, d158486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158194, d158486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158195 q = 1) (hb : d158487 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d158195, d158487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158195, d158487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30800 (p : Pattern) (ha : d158201 p = 1) (hb : d158493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d158074 q = 1) (hb : d158322 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d158074, d158322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30769 q ha hb
    | true =>
      simp only [d158074, d158322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30775 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d158101 q = 1) (hb : d158362 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d158101, d158362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158101, d158362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30781 q ha hb
  have h3 (q : Pattern) (ha : d158102 q = 1) (hb : d158363 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d158102, d158363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d158102, d158363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d158129 q = 1) (hb : d158403 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d158129, d158403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158129, d158403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30787 q ha hb
  have h5 (q : Pattern) (ha : d158130 q = 1) (hb : d158404 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d158130, d158404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158130, d158404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d158131 q = 1) (hb : d158405 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d158131, d158405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158131, d158405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d158162 q = 1) (hb : d158445 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d158162, d158445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158162, d158445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30793 q ha hb
  have h8 (q : Pattern) (ha : d158163 q = 1) (hb : d158446 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d158163, d158446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158163, d158446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d158164 q = 1) (hb : d158447 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d158164, d158447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158164, d158447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d158165 q = 1) (hb : d158448 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d158165, d158448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d158165, d158448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d158196 q = 1) (hb : d158488 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d158196, d158488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158196, d158488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30799 q ha hb
  have h12 (q : Pattern) (ha : d158197 q = 1) (hb : d158489 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d158197, d158489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158197, d158489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d158198 q = 1) (hb : d158490 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d158198, d158490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158198, d158490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d158199 q = 1) (hb : d158491 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d158199, d158491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158199, d158491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d158200 q = 1) (hb : d158492 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d158200, d158492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d158200, d158492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d158201 q = 1) (hb : d158493 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d158201, d158493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d158201, d158493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro30801 (p : Pattern) (ha : d158207 p = 1) (hb : d158499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158202 q = 1) (hb : d158494 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d158202, d158494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30800 q ha hb
    | true =>
      simp only [d158202, d158494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d158203 q = 1) (hb : d158495 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d158203, d158495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158203, d158495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d158204 q = 1) (hb : d158496 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d158204, d158496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d158204, d158496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d158205 q = 1) (hb : d158497 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d158205, d158497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158205, d158497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d158206 q = 1) (hb : d158498 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d158206, d158498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158206, d158498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d158207 q = 1) (hb : d158499 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d158207, d158499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d158207, d158499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30802 (p : Pattern) (ha : d158213 p = 1) (hb : d158505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158208 q = 1) (hb : d158500 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d158208, d158500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30801 q ha hb
    | true =>
      simp only [d158208, d158500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d158209 q = 1) (hb : d158501 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d158209, d158501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158209, d158501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d158210 q = 1) (hb : d158502 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d158210, d158502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d158210, d158502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d158211 q = 1) (hb : d158503 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d158211, d158503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158211, d158503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d158212 q = 1) (hb : d158504 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d158212, d158504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158212, d158504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d158213 q = 1) (hb : d158505 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d158213, d158505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d158213, d158505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30803 (p : Pattern) (ha : d158219 p = 1) (hb : d158511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158214 q = 1) (hb : d158506 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d158214, d158506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30802 q ha hb
    | true =>
      simp only [d158214, d158506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d158215 q = 1) (hb : d158507 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d158215, d158507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158215, d158507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d158216 q = 1) (hb : d158508 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d158216, d158508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d158216, d158508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d158217 q = 1) (hb : d158509 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d158217, d158509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158217, d158509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d158218 q = 1) (hb : d158510 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d158218, d158510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158218, d158510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d158219 q = 1) (hb : d158511 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d158219, d158511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d158219, d158511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30804 (p : Pattern) (ha : d158225 p = 1) (hb : d158517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158220 q = 1) (hb : d158512 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d158220, d158512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30803 q ha hb
    | true =>
      simp only [d158220, d158512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d158221 q = 1) (hb : d158513 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d158221, d158513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158221, d158513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d158222 q = 1) (hb : d158514 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d158222, d158514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d158222, d158514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d158223 q = 1) (hb : d158515 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d158223, d158515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158223, d158515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d158224 q = 1) (hb : d158516 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d158224, d158516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158224, d158516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d158225 q = 1) (hb : d158517 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d158225, d158517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d158225, d158517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30805 (p : Pattern) (ha : d158231 p = 1) (hb : d158523 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158226 q = 1) (hb : d158518 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d158226, d158518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30804 q ha hb
    | true =>
      simp only [d158226, d158518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d158227 q = 1) (hb : d158519 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d158227, d158519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158227, d158519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d158228 q = 1) (hb : d158520 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d158228, d158520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d158228, d158520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d158229 q = 1) (hb : d158521 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d158229, d158521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158229, d158521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d158230 q = 1) (hb : d158522 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d158230, d158522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158230, d158522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d158231 q = 1) (hb : d158523 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d158231, d158523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d158231, d158523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30806 (p : Pattern) (ha : d158237 p = 1) (hb : d158529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158232 q = 1) (hb : d158524 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d158232, d158524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30805 q ha hb
    | true =>
      simp only [d158232, d158524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d158233 q = 1) (hb : d158525 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d158233, d158525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158233, d158525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d158234 q = 1) (hb : d158526 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d158234, d158526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d158234, d158526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d158235 q = 1) (hb : d158527 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d158235, d158527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158235, d158527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d158236 q = 1) (hb : d158528 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d158236, d158528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158236, d158528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d158237 q = 1) (hb : d158529 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d158237, d158529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d158237, d158529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30807 (p : Pattern) (ha : d158243 p = 1) (hb : d158535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d158238 q = 1) (hb : d158530 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d158238, d158530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30806 q ha hb
    | true =>
      simp only [d158238, d158530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d158239 q = 1) (hb : d158531 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d158239, d158531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d158239, d158531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d158240 q = 1) (hb : d158532 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d158240, d158532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d158240, d158532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d158241 q = 1) (hb : d158533 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d158241, d158533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d158241, d158533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d158242 q = 1) (hb : d158534 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d158242, d158534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d158242, d158534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d158243 q = 1) (hb : d158535 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d158243, d158535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d158243, d158535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30808 (p : Pattern) (ha : d12227 p = 1) (hb : d122305 p = 1) : d158538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4819 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21882 q ha hb
    | true =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4820 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4821 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d122305 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12225 q = 1) (hb : d122305 q = 1) : d158536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d158536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12225, d158536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d122305 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12226 q = 1) (hb : d122305 q = 1) : d158537 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12226, d158537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12226, d158537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12227 q = 1) (hb : d122305 q = 1) : d158538 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12227, d158538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12227, d158538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro30809 (p : Pattern) (ha : d12233 p = 1) (hb : d122305 p = 1) : d158544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30808 q ha hb
    | true =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d122305 q = 1) : d158542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12232 q = 1) (hb : d122305 q = 1) : d158543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d158543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12232, d158543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12233 q = 1) (hb : d122305 q = 1) : d158544 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12233, d158544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12233, d158544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30810 (p : Pattern) (ha : d115242 p = 1) (hb : d122305 p = 1) : d158550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d122305 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d122305 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d122305 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12234 q = 1) (hb : d122305 q = 1) : d158545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30809 q ha hb
    | true =>
      simp only [d12234, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115238 q = 1) (hb : d122305 q = 1) : d158546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d158546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115238, d158546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d122305 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115239 q = 1) (hb : d122305 q = 1) : d158547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d158547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115239, d158547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115240 q = 1) (hb : d122305 q = 1) : d158548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d158548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115240, d158548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115241 q = 1) (hb : d122305 q = 1) : d158549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d158549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115241, d158549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115242 q = 1) (hb : d122305 q = 1) : d158550 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115242, d158550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115242, d158550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30811 (p : Pattern) (ha : d12240 p = 1) (hb : d122305 p = 1) : d158551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30808 q ha hb
    | true =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d122305 q = 1) : d158542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12232 q = 1) (hb : d122305 q = 1) : d158543 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12232, d158543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12232, d158543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12240 q = 1) (hb : d122305 q = 1) : d158551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12240, d158551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12240, d158551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30812 (p : Pattern) (ha : d115247 p = 1) (hb : d122305 p = 1) : d158557 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d122305 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d122305 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d122305 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d12234 q = 1) (hb : d122305 q = 1) : d158545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30809 q ha hb
    | true =>
      simp only [d12234, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115238 q = 1) (hb : d122305 q = 1) : d158546 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115238, d158546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115238, d158546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d122305 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115239 q = 1) (hb : d122305 q = 1) : d158547 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115239, d158547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115239, d158547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115240 q = 1) (hb : d122305 q = 1) : d158548 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115240, d158548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115240, d158548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115241 q = 1) (hb : d122305 q = 1) : d158549 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115241, d158549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115241, d158549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d122305 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d122305 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d122305 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d12241 q = 1) (hb : d122305 q = 1) : d158552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30811 q ha hb
    | true =>
      simp only [d12241, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115243 q = 1) (hb : d122305 q = 1) : d158553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d158553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115243, d158553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d122305 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d115244 q = 1) (hb : d122305 q = 1) : d158554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d158554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115244, d158554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115245 q = 1) (hb : d122305 q = 1) : d158555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115245, d158555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115245, d158555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115246 q = 1) (hb : d122305 q = 1) : d158556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115246, d158556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115246, d158556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d115247 q = 1) (hb : d122305 q = 1) : d158557 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115247, d158557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115247, d158557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30813 (p : Pattern) (ha : d115254 p = 1) (hb : d122305 p = 1) : d158564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d122305 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12241 q = 1) (hb : d122305 q = 1) : d158552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30811 q ha hb
    | true =>
      simp only [d12241, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115243 q = 1) (hb : d122305 q = 1) : d158553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115243, d158553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115243, d158553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d122305 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115244 q = 1) (hb : d122305 q = 1) : d158554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115244, d158554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115244, d158554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115252 q = 1) (hb : d122305 q = 1) : d158562 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115252, d158562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115252, d158562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115253 q = 1) (hb : d122305 q = 1) : d158563 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115253, d158563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115253, d158563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115254 q = 1) (hb : d122305 q = 1) : d158564 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115254, d158564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115254, d158564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30814 (p : Pattern) (ha : d12261 p = 1) (hb : d122305 p = 1) : d158572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6079 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21904 q ha hb
    | true =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6080 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6081 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d122305 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12259 q = 1) (hb : d122305 q = 1) : d158570 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d158570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12259, d158570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d122305 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12260 q = 1) (hb : d122305 q = 1) : d158571 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12260, d158571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12260, d158571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12261 q = 1) (hb : d122305 q = 1) : d158572 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12261, d158572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12261, d158572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro30815 (p : Pattern) (ha : d12267 p = 1) (hb : d122305 p = 1) : d158578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d122305 q = 1) : d158573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d158573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30814 q ha hb
    | true =>
      simp only [d12262, d158573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d122305 q = 1) : d158574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d158574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d158574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d122305 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12264 q = 1) (hb : d122305 q = 1) : d158575 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12264, d158575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12264, d158575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12265 q = 1) (hb : d122305 q = 1) : d158576 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12265, d158576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12265, d158576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12266 q = 1) (hb : d122305 q = 1) : d158577 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12266, d158577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12266, d158577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12267 q = 1) (hb : d122305 q = 1) : d158578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12267, d158578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12267, d158578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30816 (p : Pattern) (ha : d115264 p = 1) (hb : d122305 p = 1) : d158584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d122305 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12268 q = 1) (hb : d122305 q = 1) : d158579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d158579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30815 q ha hb
    | true =>
      simp only [d12268, d158579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115260 q = 1) (hb : d122305 q = 1) : d158580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115260, d158580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115260, d158580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d122305 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115261 q = 1) (hb : d122305 q = 1) : d158581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115261, d158581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115261, d158581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115262 q = 1) (hb : d122305 q = 1) : d158582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115262, d158582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115262, d158582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115263 q = 1) (hb : d122305 q = 1) : d158583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115263, d158583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115263, d158583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115264 q = 1) (hb : d122305 q = 1) : d158584 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115264, d158584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115264, d158584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30817 (p : Pattern) (ha : d115270 p = 1) (hb : d122305 p = 1) : d158590 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d122305 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115248 q = 1) (hb : d122305 q = 1) : d158558 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115248, d158558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30810 q ha hb
    | true =>
      simp only [d115248, d158558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30812 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d122305 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115249 q = 1) (hb : d122305 q = 1) : d158559 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115249, d158559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115249, d158559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115250 q = 1) (hb : d122305 q = 1) : d158560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115250, d158560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115250, d158560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115251 q = 1) (hb : d122305 q = 1) : d158561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115251, d158561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115251, d158561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115255 q = 1) (hb : d122305 q = 1) : d158565 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115255, d158565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115255, d158565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30813 q ha hb
  have h8 (q : Pattern) (ha : d115256 q = 1) (hb : d122305 q = 1) : d158566 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115256, d158566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115256, d158566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d115257 q = 1) (hb : d122305 q = 1) : d158567 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115257, d158567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115257, d158567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d115258 q = 1) (hb : d122305 q = 1) : d158568 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115258, d158568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115258, d158568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115259 q = 1) (hb : d122305 q = 1) : d158569 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115259, d158569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115259, d158569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115265 q = 1) (hb : d122305 q = 1) : d158585 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115265, d158585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115265, d158585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30816 q ha hb
  have h13 (q : Pattern) (ha : d115266 q = 1) (hb : d122305 q = 1) : d158586 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115266, d158586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115266, d158586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d115267 q = 1) (hb : d122305 q = 1) : d158587 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115267, d158587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115267, d158587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d115268 q = 1) (hb : d122305 q = 1) : d158588 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115268, d158588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115268, d158588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d115269 q = 1) (hb : d122305 q = 1) : d158589 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115269, d158589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115269, d158589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115270 q = 1) (hb : d122305 q = 1) : d158590 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115270, d158590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115270, d158590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro30818 (p : Pattern) (ha : d12289 p = 1) (hb : d122305 p = 1) : d158600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122305 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d122305 q = 1) : d158545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30809 q ha hb
    | true =>
      simp only [d12234, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d122305 q = 1) : d158596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d122305 q = 1) : d158597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d122305 q = 1) : d158598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d122305 q = 1) : d158599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12289 q = 1) (hb : d122305 q = 1) : d158600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d158600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d158600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30819 (p : Pattern) (ha : d12296 p = 1) (hb : d122305 p = 1) : d158607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122305 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d122305 q = 1) : d158545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30809 q ha hb
    | true =>
      simp only [d12234, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d122305 q = 1) : d158596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d122305 q = 1) : d158597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d122305 q = 1) : d158598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d122305 q = 1) : d158599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d122305 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12241 q = 1) (hb : d122305 q = 1) : d158552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30811 q ha hb
    | true =>
      simp only [d12241, d158552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12292 q = 1) (hb : d122305 q = 1) : d158603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d158603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12293 q = 1) (hb : d122305 q = 1) : d158604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12293, d158604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12294 q = 1) (hb : d122305 q = 1) : d158605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d158605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12295 q = 1) (hb : d122305 q = 1) : d158606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d158606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12296 q = 1) (hb : d122305 q = 1) : d158607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d158607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12296, d158607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro30820 (p : Pattern) (ha : d12373 p = 1) (hb : d122305 p = 1) : d158664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122305 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d122305 q = 1) : d158545 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30809 q ha hb
    | true =>
      simp only [d12234, d158545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d122305 q = 1) : d158596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d158596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d122305 q = 1) : d158597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d158597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d122305 q = 1) : d158598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d158598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d122305 q = 1) : d158599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d158599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d122305 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12373 q = 1) (hb : d122305 q = 1) : d158664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12373, d158664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12373, d158664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30821 (p : Pattern) (ha : d12301 p = 1) (hb : d122305 p = 1) : d158612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30808 q ha hb
    | true =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d122305 q = 1) : d158542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12300 q = 1) (hb : d122305 q = 1) : d158611 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d158611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d158611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12301 q = 1) (hb : d122305 q = 1) : d158612 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12301, d158612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12301, d158612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30822 (p : Pattern) (ha : d12308 p = 1) (hb : d122305 p = 1) : d158619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30808 q ha hb
    | true =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12306 q = 1) (hb : d122305 q = 1) : d158617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d158617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d158617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12307 q = 1) (hb : d122305 q = 1) : d158618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d158618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12307, d158618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12308 q = 1) (hb : d122305 q = 1) : d158619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12308, d158619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12308, d158619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30823 (p : Pattern) (ha : d12312 p = 1) (hb : d122305 p = 1) : d123974 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322 q = 1) : d322 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d323 q = 1) (hb : d122304 q = 1) : d14077 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d323, d122304, d14077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12312 q = 1) (hb : d122305 q = 1) : d123974 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12312, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12312, d122305, d123974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30824 (p : Pattern) (ha : d12318 p = 1) (hb : d122305 p = 1) : d158625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30823 q ha hb
    | true =>
      simp only [d12313, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21882 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4819 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21882 q ha hb
    | true =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4820 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4821 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12316 q = 1) (hb : d122305 q = 1) : d158623 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d158623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12316, d158623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d122305 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12225 q = 1) (hb : d122305 q = 1) : d158536 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d158536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12225, d158536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12317 q = 1) (hb : d122305 q = 1) : d158624 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12317, d158624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12317, d158624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12318 q = 1) (hb : d122305 q = 1) : d158625 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12318, d158625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12318, d158625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro30825 (p : Pattern) (ha : d12324 p = 1) (hb : d122305 p = 1) : d158631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d122305 q = 1) : d158626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d158626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30824 q ha hb
    | true =>
      simp only [d12319, d158626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d122305 q = 1) : d158627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d158627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d158627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30808 q ha hb
    | true =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d122305 q = 1) : d158628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d158628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d158628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d122305 q = 1) : d158629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d158629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d158629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d122305 q = 1) : d158630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d158630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d158630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12324 q = 1) (hb : d122305 q = 1) : d158631 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12324, d158631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12324, d158631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30826 (p : Pattern) (ha : d12344 p = 1) (hb : d122305 p = 1) : d158637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30808 q ha hb
    | true =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d122305 q = 1) : d158634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d158634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d158634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d122305 q = 1) : d158635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d158635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d158635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d122305 q = 1) : d158636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d158636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d158636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12344 q = 1) (hb : d122305 q = 1) : d158637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12344, d158637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12344, d158637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30827 (p : Pattern) (ha : d115280 p = 1) (hb : d122305 p = 1) : d158643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d122305 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12302 q = 1) (hb : d122305 q = 1) : d158613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d158613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30821 q ha hb
    | true =>
      simp only [d12302, d158613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12303 q = 1) (hb : d122305 q = 1) : d158614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d158614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d158614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12304 q = 1) (hb : d122305 q = 1) : d158615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d158615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12304, d158615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12305 q = 1) (hb : d122305 q = 1) : d158616 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d158616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d158616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d122305 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12309 q = 1) (hb : d122305 q = 1) : d158620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d158620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30822 q ha hb
    | true =>
      simp only [d12309, d158620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12310 q = 1) (hb : d122305 q = 1) : d158621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d158621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d158621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12311 q = 1) (hb : d122305 q = 1) : d158622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d158622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12311, d158622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12325 q = 1) (hb : d122305 q = 1) : d158632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d158632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30825 q ha hb
    | true =>
      simp only [d12325, d158632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30809 q ha hb
  have h11 (q : Pattern) (ha : d115276 q = 1) (hb : d122305 q = 1) : d158633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d158633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115276, d158633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12345 q = 1) (hb : d122305 q = 1) : d158638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d158638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30826 q ha hb
    | true =>
      simp only [d12345, d158638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12346 q = 1) (hb : d122305 q = 1) : d158639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d158639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12346, d158639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115277 q = 1) (hb : d122305 q = 1) : d158640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d158640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115277, d158640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115278 q = 1) (hb : d122305 q = 1) : d158641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d158641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115278, d158641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115279 q = 1) (hb : d122305 q = 1) : d158642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d158642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115279, d158642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115280 q = 1) (hb : d122305 q = 1) : d158643 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d158643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115280, d158643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro30828 (p : Pattern) (ha : d12351 p = 1) (hb : d122305 p = 1) : d158644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30808 q ha hb
    | true =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d122305 q = 1) : d158542 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d158542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12300 q = 1) (hb : d122305 q = 1) : d158611 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d158611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d158611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12351 q = 1) (hb : d122305 q = 1) : d158644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12351, d158644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12351, d158644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30829 (p : Pattern) (ha : d12356 p = 1) (hb : d122305 p = 1) : d158649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30808 q ha hb
    | true =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122305 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d122305 q = 1) : d158541 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d158541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12306 q = 1) (hb : d122305 q = 1) : d158617 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d158617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d158617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12307 q = 1) (hb : d122305 q = 1) : d158618 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d158618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12307, d158618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12356 q = 1) (hb : d122305 q = 1) : d158649 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12356, d158649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12356, d158649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30830 (p : Pattern) (ha : d12360 p = 1) (hb : d122305 p = 1) : d158653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d122305 q = 1) : d158626 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d158626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30824 q ha hb
    | true =>
      simp only [d12319, d158626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d122305 q = 1) : d158627 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d158627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d158627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30808 q ha hb
    | true =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d122305 q = 1) : d158628 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d158628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d158628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d122305 q = 1) : d158629 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d158629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d158629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d122305 q = 1) : d158630 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d158630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d158630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12360 q = 1) (hb : d122305 q = 1) : d158653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12360, d158653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12360, d158653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30831 (p : Pattern) (ha : d12365 p = 1) (hb : d122305 p = 1) : d158656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d122305 q = 1) : d158539 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30808 q ha hb
    | true =>
      simp only [d12228, d158539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d122305 q = 1) : d158540 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d158540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d122305 q = 1) : d158634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d158634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d158634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d122305 q = 1) : d158635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d158635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d158635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d122305 q = 1) : d158636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d158636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d158636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12365 q = 1) (hb : d122305 q = 1) : d158656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12365, d158656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12365, d158656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30832 (p : Pattern) (ha : d115285 p = 1) (hb : d122305 p = 1) : d158662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d122305 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12302 q = 1) (hb : d122305 q = 1) : d158613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d158613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30821 q ha hb
    | true =>
      simp only [d12302, d158613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12303 q = 1) (hb : d122305 q = 1) : d158614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d158614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d158614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12304 q = 1) (hb : d122305 q = 1) : d158615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d158615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12304, d158615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12305 q = 1) (hb : d122305 q = 1) : d158616 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d158616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d158616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d122305 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12309 q = 1) (hb : d122305 q = 1) : d158620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d158620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30822 q ha hb
    | true =>
      simp only [d12309, d158620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12310 q = 1) (hb : d122305 q = 1) : d158621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d158621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d158621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12311 q = 1) (hb : d122305 q = 1) : d158622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d158622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12311, d158622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12325 q = 1) (hb : d122305 q = 1) : d158632 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d158632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30825 q ha hb
    | true =>
      simp only [d12325, d158632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30809 q ha hb
  have h11 (q : Pattern) (ha : d115276 q = 1) (hb : d122305 q = 1) : d158633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d158633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115276, d158633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12345 q = 1) (hb : d122305 q = 1) : d158638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d158638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30826 q ha hb
    | true =>
      simp only [d12345, d158638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12346 q = 1) (hb : d122305 q = 1) : d158639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d158639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12346, d158639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115277 q = 1) (hb : d122305 q = 1) : d158640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d158640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115277, d158640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115278 q = 1) (hb : d122305 q = 1) : d158641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d158641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115278, d158641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115279 q = 1) (hb : d122305 q = 1) : d158642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d158642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115279, d158642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d122305 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12352 q = 1) (hb : d122305 q = 1) : d158645 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12352, d158645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30828 q ha hb
    | true =>
      simp only [d12352, d158645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12353 q = 1) (hb : d122305 q = 1) : d158646 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12353, d158646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12353, d158646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12354 q = 1) (hb : d122305 q = 1) : d158647 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12354, d158647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12354, d158647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12355 q = 1) (hb : d122305 q = 1) : d158648 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12355, d158648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12355, d158648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d122305 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12357 q = 1) (hb : d122305 q = 1) : d158650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12357, d158650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30829 q ha hb
    | true =>
      simp only [d12357, d158650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12358 q = 1) (hb : d122305 q = 1) : d158651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12358, d158651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12358, d158651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12359 q = 1) (hb : d122305 q = 1) : d158652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12359, d158652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12359, d158652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12361 q = 1) (hb : d122305 q = 1) : d158654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d158654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30830 q ha hb
    | true =>
      simp only [d12361, d158654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30811 q ha hb
  have h27 (q : Pattern) (ha : d115281 q = 1) (hb : d122305 q = 1) : d158655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d158655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d115281, d158655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d12366 q = 1) (hb : d122305 q = 1) : d158657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d158657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30831 q ha hb
    | true =>
      simp only [d12366, d158657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12367 q = 1) (hb : d122305 q = 1) : d158658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d158658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12367, d158658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d115282 q = 1) (hb : d122305 q = 1) : d158659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d158659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115282, d158659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d115283 q = 1) (hb : d122305 q = 1) : d158660 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d158660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d115283, d158660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d115284 q = 1) (hb : d122305 q = 1) : d158661 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d158661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115284, d158661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d115285 q = 1) (hb : d122305 q = 1) : d158662 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d158662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115285, d158662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro30833 (p : Pattern) (ha : d115292 p = 1) (hb : d122305 p = 1) : d158671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12361 q = 1) (hb : d122305 q = 1) : d158654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d158654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30830 q ha hb
    | true =>
      simp only [d12361, d158654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30811 q ha hb
  have h2 (q : Pattern) (ha : d115281 q = 1) (hb : d122305 q = 1) : d158655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d158655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115281, d158655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12366 q = 1) (hb : d122305 q = 1) : d158657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d158657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30831 q ha hb
    | true =>
      simp only [d12366, d158657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12367 q = 1) (hb : d122305 q = 1) : d158658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d158658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12367, d158658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115282 q = 1) (hb : d122305 q = 1) : d158659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d158659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115282, d158659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115290 q = 1) (hb : d122305 q = 1) : d158669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d158669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115290, d158669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115291 q = 1) (hb : d122305 q = 1) : d158670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d158670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115291, d158670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115292 q = 1) (hb : d122305 q = 1) : d158671 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d158671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115292, d158671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30834 (p : Pattern) (ha : d12386 p = 1) (hb : d122305 p = 1) : d124032 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d415 q = 1) : d415 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d229 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d416 q = 1) (hb : d122304 q = 1) : d14154 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d416, d122304, d14154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12386 q = 1) (hb : d122305 q = 1) : d124032 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12386, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12386, d122305, d124032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30835 (p : Pattern) (ha : d12392 p = 1) (hb : d122305 p = 1) : d158679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30834 q ha hb
    | true =>
      simp only [d12387, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21904 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6079 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21904 q ha hb
    | true =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6080 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6081 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12390 q = 1) (hb : d122305 q = 1) : d158677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d158677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12390, d158677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d122305 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12259 q = 1) (hb : d122305 q = 1) : d158570 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d158570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12259, d158570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12391 q = 1) (hb : d122305 q = 1) : d158678 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12391, d158678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12391, d158678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12392 q = 1) (hb : d122305 q = 1) : d158679 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12392, d158679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d12392, d158679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro30836 (p : Pattern) (ha : d12398 p = 1) (hb : d122305 p = 1) : d158685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12393 q = 1) (hb : d122305 q = 1) : d158680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12393, d158680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30835 q ha hb
    | true =>
      simp only [d12393, d158680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12394 q = 1) (hb : d122305 q = 1) : d158681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12394, d158681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12394, d158681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12262 q = 1) (hb : d122305 q = 1) : d158573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d158573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30814 q ha hb
    | true =>
      simp only [d12262, d158573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12263 q = 1) (hb : d122305 q = 1) : d158574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d158574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d158574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12395 q = 1) (hb : d122305 q = 1) : d158682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12395, d158682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12395, d158682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12396 q = 1) (hb : d122305 q = 1) : d158683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12396, d158683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12396, d158683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12397 q = 1) (hb : d122305 q = 1) : d158684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12397, d158684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12397, d158684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12398 q = 1) (hb : d122305 q = 1) : d158685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12398, d158685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12398, d158685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30837 (p : Pattern) (ha : d12418 p = 1) (hb : d122305 p = 1) : d158691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d122305 q = 1) : d158573 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d158573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30814 q ha hb
    | true =>
      simp only [d12262, d158573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d122305 q = 1) : d158574 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d158574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d158574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12415 q = 1) (hb : d122305 q = 1) : d158688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12415, d158688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12415, d158688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12416 q = 1) (hb : d122305 q = 1) : d158689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12416, d158689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12416, d158689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12417 q = 1) (hb : d122305 q = 1) : d158690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12417, d158690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12417, d158690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12418 q = 1) (hb : d122305 q = 1) : d158691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12418, d158691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12418, d158691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30838 (p : Pattern) (ha : d115302 p = 1) (hb : d122305 p = 1) : d158697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12399 q = 1) (hb : d122305 q = 1) : d158686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12399, d158686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30836 q ha hb
    | true =>
      simp only [d12399, d158686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30815 q ha hb
  have h2 (q : Pattern) (ha : d115298 q = 1) (hb : d122305 q = 1) : d158687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d158687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115298, d158687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12419 q = 1) (hb : d122305 q = 1) : d158692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12419, d158692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30837 q ha hb
    | true =>
      simp only [d12419, d158692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12420 q = 1) (hb : d122305 q = 1) : d158693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12420, d158693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12420, d158693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115299 q = 1) (hb : d122305 q = 1) : d158694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d158694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115299, d158694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115300 q = 1) (hb : d122305 q = 1) : d158695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d158695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115300, d158695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115301 q = 1) (hb : d122305 q = 1) : d158696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d158696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115301, d158696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115302 q = 1) (hb : d122305 q = 1) : d158697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d158697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115302, d158697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30839 (p : Pattern) (ha : d115308 p = 1) (hb : d122305 p = 1) : d158703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12290 q = 1) (hb : d122305 q = 1) : d158601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12290, d158601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12290, d158601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30818 q ha hb
  have h2 (q : Pattern) (ha : d12291 q = 1) (hb : d122305 q = 1) : d158602 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12291, d158602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12291, d158602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12297 q = 1) (hb : d122305 q = 1) : d158608 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d158608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30818 q ha hb
    | true =>
      simp only [d12297, d158608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30819 q ha hb
  have h4 (q : Pattern) (ha : d12298 q = 1) (hb : d122305 q = 1) : d158609 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d158609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12298, d158609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12299 q = 1) (hb : d122305 q = 1) : d158610 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12299, d158610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12299, d158610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115286 q = 1) (hb : d122305 q = 1) : d158663 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d158663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30827 q ha hb
    | true =>
      simp only [d115286, d158663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30832 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d122305 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12374 q = 1) (hb : d122305 q = 1) : d158665 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12374, d158665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30820 q ha hb
    | true =>
      simp only [d12374, d158665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115287 q = 1) (hb : d122305 q = 1) : d158666 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d158666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115287, d158666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115288 q = 1) (hb : d122305 q = 1) : d158667 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d158667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115288, d158667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d115289 q = 1) (hb : d122305 q = 1) : d158668 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d158668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115289, d158668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115293 q = 1) (hb : d122305 q = 1) : d158672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d158672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115293, d158672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30833 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d122305 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d115294 q = 1) (hb : d122305 q = 1) : d158673 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d158673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115294, d158673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115295 q = 1) (hb : d122305 q = 1) : d158674 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d158674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115295, d158674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115296 q = 1) (hb : d122305 q = 1) : d158675 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d158675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115296, d158675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d115297 q = 1) (hb : d122305 q = 1) : d158676 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d158676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115297, d158676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115303 q = 1) (hb : d122305 q = 1) : d158698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d158698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115303, d158698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30838 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d122305 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d115304 q = 1) (hb : d122305 q = 1) : d158699 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d158699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115304, d158699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d115305 q = 1) (hb : d122305 q = 1) : d158700 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d158700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115305, d158700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115306 q = 1) (hb : d122305 q = 1) : d158701 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d158701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115306, d158701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115307 q = 1) (hb : d122305 q = 1) : d158702 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d158702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115307, d158702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d115308 q = 1) (hb : d122305 q = 1) : d158703 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d158703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115308, d158703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro30840 (p : Pattern) (ha : d115314 p = 1) (hb : d122305 p = 1) : d158709 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d122305 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115271 q = 1) (hb : d122305 q = 1) : d158591 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115271, d158591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115271, d158591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30817 q ha hb
  have h3 (q : Pattern) (ha : d115272 q = 1) (hb : d122305 q = 1) : d158592 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115272, d158592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115272, d158592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115273 q = 1) (hb : d122305 q = 1) : d158593 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115273, d158593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115273, d158593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115274 q = 1) (hb : d122305 q = 1) : d158594 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115274, d158594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115274, d158594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115275 q = 1) (hb : d122305 q = 1) : d158595 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115275, d158595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115275, d158595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115309 q = 1) (hb : d122305 q = 1) : d158704 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d158704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115309, d158704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30839 q ha hb
  have h8 (q : Pattern) (ha : d115310 q = 1) (hb : d122305 q = 1) : d158705 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d158705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115310, d158705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115311 q = 1) (hb : d122305 q = 1) : d158706 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d158706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115311, d158706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115312 q = 1) (hb : d122305 q = 1) : d158707 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d158707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115312, d158707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115313 q = 1) (hb : d122305 q = 1) : d158708 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d158708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115313, d158708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115314 q = 1) (hb : d122305 q = 1) : d158709 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d158709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115314, d158709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro30841 (p : Pattern) (ha : d12438 p = 1) (hb : d122305 p = 1) : d158711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30823 q ha hb
    | true =>
      simp only [d12313, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21882 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4819 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21882 q ha hb
    | true =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4820 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4821 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12316 q = 1) (hb : d122305 q = 1) : d158623 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d158623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12316, d158623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4822 q = 1) (hb : d122305 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4822, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12437 q = 1) (hb : d122305 q = 1) : d158710 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12437, d158710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12437, d158710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12438 q = 1) (hb : d122305 q = 1) : d158711 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12438, d158711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12438, d158711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro30842 (p : Pattern) (ha : d12442 p = 1) (hb : d122305 p = 1) : d124070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4819 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21882 q ha hb
    | true =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4820 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4821 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4822 q = 1) (hb : d122305 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4822, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12441 q = 1) (hb : d122305 q = 1) : d124069 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12441, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12441, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12442 q = 1) (hb : d122305 q = 1) : d124070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12442, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12442, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30843 (p : Pattern) (ha : d12448 p = 1) (hb : d122305 p = 1) : d158717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30841 q ha hb
    | true =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d122305 q = 1) : d158715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d122305 q = 1) : d158716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d158716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d158716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12448 q = 1) (hb : d122305 q = 1) : d158717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12448, d158717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12448, d158717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30844 (p : Pattern) (ha : d12452 p = 1) (hb : d122305 p = 1) : d124080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d122305 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d122305 q = 1) : d124079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12452 q = 1) (hb : d122305 q = 1) : d124080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12452, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12452, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30845 (p : Pattern) (ha : d12458 p = 1) (hb : d122305 p = 1) : d158723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d122305 q = 1) : d158718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30843 q ha hb
    | true =>
      simp only [d12453, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30844 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d122305 q = 1) : d158719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d122305 q = 1) : d158720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d122305 q = 1) : d158721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d122305 q = 1) : d158722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12458 q = 1) (hb : d122305 q = 1) : d158723 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12458, d158723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12458, d158723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30846 (p : Pattern) (ha : d12461 p = 1) (hb : d122305 p = 1) : d158726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30841 q ha hb
    | true =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d122305 q = 1) : d158715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12447 q = 1) (hb : d122305 q = 1) : d158716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d158716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12447, d158716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12461 q = 1) (hb : d122305 q = 1) : d158726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12461, d158726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12461, d158726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30847 (p : Pattern) (ha : d12462 p = 1) (hb : d122305 p = 1) : d124090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d122305 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d122305 q = 1) : d124079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12462 q = 1) (hb : d122305 q = 1) : d124090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12462, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12462, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30848 (p : Pattern) (ha : d12468 p = 1) (hb : d122305 p = 1) : d158732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d122305 q = 1) : d158718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30843 q ha hb
    | true =>
      simp only [d12453, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30844 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d122305 q = 1) : d158719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d122305 q = 1) : d158720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d122305 q = 1) : d158721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d122305 q = 1) : d158722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12463 q = 1) (hb : d122305 q = 1) : d158727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d158727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30846 q ha hb
    | true =>
      simp only [d12463, d158727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30847 q ha hb
  have h7 (q : Pattern) (ha : d12464 q = 1) (hb : d122305 q = 1) : d158728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d158728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12465 q = 1) (hb : d122305 q = 1) : d158729 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12465, d158729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12466 q = 1) (hb : d122305 q = 1) : d158730 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d158730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12467 q = 1) (hb : d122305 q = 1) : d158731 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d158731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12468 q = 1) (hb : d122305 q = 1) : d158732 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12468, d158732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12468, d158732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30849 (p : Pattern) (ha : d12574 p = 1) (hb : d122305 p = 1) : d158793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12453 q = 1) (hb : d122305 q = 1) : d158718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30843 q ha hb
    | true =>
      simp only [d12453, d158718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30844 q ha hb
  have h2 (q : Pattern) (ha : d12454 q = 1) (hb : d122305 q = 1) : d158719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d158719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12455 q = 1) (hb : d122305 q = 1) : d158720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12455, d158720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12456 q = 1) (hb : d122305 q = 1) : d158721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d158721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12457 q = 1) (hb : d122305 q = 1) : d158722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d158722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12569 q = 1) (hb : d122305 q = 1) : d124164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30844 q ha hb
    | true =>
      simp only [d12569, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12570 q = 1) (hb : d122305 q = 1) : d124165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12571 q = 1) (hb : d122305 q = 1) : d124166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12571, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12572 q = 1) (hb : d122305 q = 1) : d124167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12573 q = 1) (hb : d122305 q = 1) : d124168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12574 q = 1) (hb : d122305 q = 1) : d158793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12574, d158793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12574, d158793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30850 (p : Pattern) (ha : d12580 p = 1) (hb : d122305 p = 1) : d124175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12569 q = 1) (hb : d122305 q = 1) : d124164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30844 q ha hb
    | true =>
      simp only [d12569, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12570 q = 1) (hb : d122305 q = 1) : d124165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12571 q = 1) (hb : d122305 q = 1) : d124166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12571, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12572 q = 1) (hb : d122305 q = 1) : d124167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12573 q = 1) (hb : d122305 q = 1) : d124168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12575 q = 1) (hb : d122305 q = 1) : d124170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30847 q ha hb
    | true =>
      simp only [d12575, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12576 q = 1) (hb : d122305 q = 1) : d124171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12577 q = 1) (hb : d122305 q = 1) : d124172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12577, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12578 q = 1) (hb : d122305 q = 1) : d124173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12579 q = 1) (hb : d122305 q = 1) : d124174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12580 q = 1) (hb : d122305 q = 1) : d124175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12580, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12580, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30851 (p : Pattern) (ha : d12589 p = 1) (hb : d122305 p = 1) : d124184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12575 q = 1) (hb : d122305 q = 1) : d124170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30847 q ha hb
    | true =>
      simp only [d12575, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12576 q = 1) (hb : d122305 q = 1) : d124171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12577 q = 1) (hb : d122305 q = 1) : d124172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12577, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12578 q = 1) (hb : d122305 q = 1) : d124173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12579 q = 1) (hb : d122305 q = 1) : d124174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12589 q = 1) (hb : d122305 q = 1) : d124184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12589, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12589, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30852 (p : Pattern) (ha : d12622 p = 1) (hb : d122305 p = 1) : d124204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6079 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21904 q ha hb
    | true =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6080 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6081 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6082 q = 1) (hb : d122305 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6082, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12621 q = 1) (hb : d122305 q = 1) : d124203 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12621, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12621, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12622 q = 1) (hb : d122305 q = 1) : d124204 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12622, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12622, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30853 (p : Pattern) (ha : d12668 p = 1) (hb : d122305 p = 1) : d124227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12623 q = 1) (hb : d122305 q = 1) : d124205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30852 q ha hb
    | true =>
      simp only [d12623, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12624 q = 1) (hb : d122305 q = 1) : d124206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12665 q = 1) (hb : d122305 q = 1) : d124224 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12665, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12665, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12666 q = 1) (hb : d122305 q = 1) : d124225 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12666, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12666, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12667 q = 1) (hb : d122305 q = 1) : d124226 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12667, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12667, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12668 q = 1) (hb : d122305 q = 1) : d124227 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12668, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12668, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30854 (p : Pattern) (ha : d12674 p = 1) (hb : d122305 p = 1) : d124233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12669 q = 1) (hb : d122305 q = 1) : d124228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12669, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30853 q ha hb
    | true =>
      simp only [d12669, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12670 q = 1) (hb : d122305 q = 1) : d124229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12670, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12670, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12671 q = 1) (hb : d122305 q = 1) : d124230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12671, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12671, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12672 q = 1) (hb : d122305 q = 1) : d124231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12672, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12672, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12673 q = 1) (hb : d122305 q = 1) : d124232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12673, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12673, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12674 q = 1) (hb : d122305 q = 1) : d124233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12674, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12674, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30855 (p : Pattern) (ha : d12473 p = 1) (hb : d122305 p = 1) : d158737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30841 q ha hb
    | true =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d122305 q = 1) : d158715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d122305 q = 1) : d158736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d158736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d158736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12473 q = 1) (hb : d122305 q = 1) : d158737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12473, d158737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12473, d158737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30856 (p : Pattern) (ha : d12475 p = 1) (hb : d122305 p = 1) : d124103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d122305 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d122305 q = 1) : d124102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12475 q = 1) (hb : d122305 q = 1) : d124103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12475, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12475, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30857 (p : Pattern) (ha : d12482 p = 1) (hb : d122305 p = 1) : d158744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30841 q ha hb
    | true =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d122305 q = 1) : d158742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d158742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d158742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d122305 q = 1) : d158743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d158743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d158743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12482 q = 1) (hb : d122305 q = 1) : d158744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12482, d158744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12482, d158744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30858 (p : Pattern) (ha : d12485 p = 1) (hb : d122305 p = 1) : d124113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d122305 q = 1) : d124111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d122305 q = 1) : d124112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d122305 q = 1) : d124113 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12485, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12485, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30859 (p : Pattern) (ha : d12489 p = 1) (hb : d122305 p = 1) : d124117 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d546 q = 1) : d546 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d547 q = 1) (hb : d122304 q = 1) : d14261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d122304, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d547, d122304, d14261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12489 q = 1) (hb : d122305 q = 1) : d124117 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12489, d122305, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12489, d122305, d124117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30860 (p : Pattern) (ha : d12496 p = 1) (hb : d122305 p = 1) : d158748 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d12494 q = 1) : d12494 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12495 q = 1) (hb : d122304 q = 1) : d14078 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d122304, d14078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12495, d122304, d14078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12496 q = 1) (hb : d122305 q = 1) : d158748 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12496, d122305, d158748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12496, d122305, d158748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30861 (p : Pattern) (ha : d12502 p = 1) (hb : d122305 p = 1) : d158754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12490 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12490, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30859 q ha hb
    | true =>
      simp only [d12490, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30823 q ha hb
  have h2 (q : Pattern) (ha : d12491 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12491, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12491, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12492 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12492, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12492, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12497 q = 1) (hb : d122305 q = 1) : d158749 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12497, d158749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30823 q ha hb
    | true =>
      simp only [d12497, d158749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30860 q ha hb
  have h5 (q : Pattern) (ha : d12498 q = 1) (hb : d122305 q = 1) : d158750 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12498, d158750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12498, d158750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12499 q = 1) (hb : d122305 q = 1) : d158751 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12499, d158751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12499, d158751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12500 q = 1) (hb : d122305 q = 1) : d158752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12500, d158752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12500, d158752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12313 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30823 q ha hb
    | true =>
      simp only [d12313, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21882 q ha hb
  have h9 (q : Pattern) (ha : d12314 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12315 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4819 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21882 q ha hb
    | true =>
      simp only [d4819, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4820 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4821 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12316 q = 1) (hb : d122305 q = 1) : d158623 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d158623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12316, d158623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12501 q = 1) (hb : d122305 q = 1) : d158753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12501, d158753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12501, d158753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12502 q = 1) (hb : d122305 q = 1) : d158754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12502, d158754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12502, d158754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro30862 (p : Pattern) (ha : d12508 p = 1) (hb : d122305 p = 1) : d158760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d122305 q = 1) : d158755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d158755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30861 q ha hb
    | true =>
      simp only [d12503, d158755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d122305 q = 1) : d158756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d158756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d158756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30841 q ha hb
    | true =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d122305 q = 1) : d158757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d158757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d158757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d122305 q = 1) : d158758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d158758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d158758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d122305 q = 1) : d158759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d158759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d158759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12508 q = 1) (hb : d122305 q = 1) : d158760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12508, d158760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12508, d158760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30863 (p : Pattern) (ha : d12537 p = 1) (hb : d122305 p = 1) : d158766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30841 q ha hb
    | true =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d122305 q = 1) : d158763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d158763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d158763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d122305 q = 1) : d158764 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d158764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d158764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d122305 q = 1) : d158765 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d158765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d158765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12537 q = 1) (hb : d122305 q = 1) : d158766 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12537, d158766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12537, d158766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30864 (p : Pattern) (ha : d115319 p = 1) (hb : d122305 p = 1) : d158772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d122305 q = 1) : d158738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d158738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30855 q ha hb
    | true =>
      simp only [d12476, d158738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30856 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d122305 q = 1) : d158739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d158739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d158739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d122305 q = 1) : d158740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d158740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d158740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d122305 q = 1) : d158741 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d158741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d158741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d122305 q = 1) : d158745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d158745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30857 q ha hb
    | true =>
      simp only [d12486, d158745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30858 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d122305 q = 1) : d158746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d158746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d158746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d122305 q = 1) : d158747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d158747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d158747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d122305 q = 1) : d158761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d158761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30862 q ha hb
    | true =>
      simp only [d12509, d158761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30843 q ha hb
  have h9 (q : Pattern) (ha : d115315 q = 1) (hb : d122305 q = 1) : d158762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d158762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115315, d158762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d122305 q = 1) : d158767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d158767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30863 q ha hb
    | true =>
      simp only [d12538, d158767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d122305 q = 1) : d158768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d158768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d158768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115316 q = 1) (hb : d122305 q = 1) : d158769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d158769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d158769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115317 q = 1) (hb : d122305 q = 1) : d158770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d158770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115317, d158770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115318 q = 1) (hb : d122305 q = 1) : d158771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d158771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115318, d158771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115319 q = 1) (hb : d122305 q = 1) : d158772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d158772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115319, d158772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30865 (p : Pattern) (ha : d12544 p = 1) (hb : d122305 p = 1) : d158773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30841 q ha hb
    | true =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12446 q = 1) (hb : d122305 q = 1) : d158715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12446, d158715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12472 q = 1) (hb : d122305 q = 1) : d158736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d158736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d158736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12544 q = 1) (hb : d122305 q = 1) : d158773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12544, d158773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12544, d158773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30866 (p : Pattern) (ha : d12545 p = 1) (hb : d122305 p = 1) : d124143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d122305 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d122305 q = 1) : d124102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12545 q = 1) (hb : d122305 q = 1) : d124143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12545, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12545, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30867 (p : Pattern) (ha : d12550 p = 1) (hb : d122305 p = 1) : d158778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30841 q ha hb
    | true =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12445 q = 1) (hb : d122305 q = 1) : d158714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d158714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12480 q = 1) (hb : d122305 q = 1) : d158742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d158742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d158742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12481 q = 1) (hb : d122305 q = 1) : d158743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d158743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12481, d158743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12550 q = 1) (hb : d122305 q = 1) : d158778 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12550, d158778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12550, d158778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30868 (p : Pattern) (ha : d12551 p = 1) (hb : d122305 p = 1) : d124149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d122305 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30842 q ha hb
    | true =>
      simp only [d12443, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d122305 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d122305 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d122305 q = 1) : d124111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d122305 q = 1) : d124112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12551 q = 1) (hb : d122305 q = 1) : d124149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12551, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12551, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30869 (p : Pattern) (ha : d12555 p = 1) (hb : d122305 p = 1) : d158782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d122305 q = 1) : d158755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d158755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30861 q ha hb
    | true =>
      simp only [d12503, d158755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d122305 q = 1) : d158756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d158756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d158756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30841 q ha hb
    | true =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d122305 q = 1) : d158757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d158757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d158757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d122305 q = 1) : d158758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d158758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d158758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d122305 q = 1) : d158759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d158759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d158759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12555 q = 1) (hb : d122305 q = 1) : d158782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12555, d158782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12555, d158782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30870 (p : Pattern) (ha : d12561 p = 1) (hb : d122305 p = 1) : d158785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d122305 q = 1) : d158712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30841 q ha hb
    | true =>
      simp only [d12439, d158712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d122305 q = 1) : d158713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d158713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d122305 q = 1) : d158763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d158763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d158763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d122305 q = 1) : d158764 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d158764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d158764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d122305 q = 1) : d158765 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d158765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d158765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12561 q = 1) (hb : d122305 q = 1) : d158785 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12561, d158785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12561, d158785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30871 (p : Pattern) (ha : d115324 p = 1) (hb : d122305 p = 1) : d158791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12476 q = 1) (hb : d122305 q = 1) : d158738 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d158738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30855 q ha hb
    | true =>
      simp only [d12476, d158738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30856 q ha hb
  have h2 (q : Pattern) (ha : d12477 q = 1) (hb : d122305 q = 1) : d158739 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d158739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d158739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12478 q = 1) (hb : d122305 q = 1) : d158740 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d158740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12478, d158740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12479 q = 1) (hb : d122305 q = 1) : d158741 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d158741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d158741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12486 q = 1) (hb : d122305 q = 1) : d158745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d158745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30857 q ha hb
    | true =>
      simp only [d12486, d158745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30858 q ha hb
  have h6 (q : Pattern) (ha : d12487 q = 1) (hb : d122305 q = 1) : d158746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d158746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d158746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12488 q = 1) (hb : d122305 q = 1) : d158747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d158747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12488, d158747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12509 q = 1) (hb : d122305 q = 1) : d158761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d158761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30862 q ha hb
    | true =>
      simp only [d12509, d158761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30843 q ha hb
  have h9 (q : Pattern) (ha : d115315 q = 1) (hb : d122305 q = 1) : d158762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d158762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115315, d158762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12538 q = 1) (hb : d122305 q = 1) : d158767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d158767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30863 q ha hb
    | true =>
      simp only [d12538, d158767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12539 q = 1) (hb : d122305 q = 1) : d158768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d158768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12539, d158768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115316 q = 1) (hb : d122305 q = 1) : d158769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d158769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115316, d158769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115317 q = 1) (hb : d122305 q = 1) : d158770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d158770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115317, d158770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115318 q = 1) (hb : d122305 q = 1) : d158771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d158771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115318, d158771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12546 q = 1) (hb : d122305 q = 1) : d158774 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12546, d158774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30865 q ha hb
    | true =>
      simp only [d12546, d158774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30866 q ha hb
  have h16 (q : Pattern) (ha : d12547 q = 1) (hb : d122305 q = 1) : d158775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12547, d158775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12547, d158775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12548 q = 1) (hb : d122305 q = 1) : d158776 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12548, d158776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12548, d158776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12549 q = 1) (hb : d122305 q = 1) : d158777 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12549, d158777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12549, d158777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12552 q = 1) (hb : d122305 q = 1) : d158779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12552, d158779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30867 q ha hb
    | true =>
      simp only [d12552, d158779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30868 q ha hb
  have h20 (q : Pattern) (ha : d12553 q = 1) (hb : d122305 q = 1) : d158780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12553, d158780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12553, d158780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12554 q = 1) (hb : d122305 q = 1) : d158781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12554, d158781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12554, d158781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12556 q = 1) (hb : d122305 q = 1) : d158783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d158783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30869 q ha hb
    | true =>
      simp only [d12556, d158783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30846 q ha hb
  have h23 (q : Pattern) (ha : d115320 q = 1) (hb : d122305 q = 1) : d158784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d158784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115320, d158784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12562 q = 1) (hb : d122305 q = 1) : d158786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d158786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30870 q ha hb
    | true =>
      simp only [d12562, d158786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12563 q = 1) (hb : d122305 q = 1) : d158787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d158787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12563, d158787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115321 q = 1) (hb : d122305 q = 1) : d158788 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d158788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115321, d158788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115322 q = 1) (hb : d122305 q = 1) : d158789 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d158789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115322, d158789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115323 q = 1) (hb : d122305 q = 1) : d158790 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d158790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115323, d158790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115324 q = 1) (hb : d122305 q = 1) : d158791 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d158791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115324, d158791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro30872 (p : Pattern) (ha : d115331 p = 1) (hb : d122305 p = 1) : d158800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12556 q = 1) (hb : d122305 q = 1) : d158783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d158783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30869 q ha hb
    | true =>
      simp only [d12556, d158783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30846 q ha hb
  have h2 (q : Pattern) (ha : d115320 q = 1) (hb : d122305 q = 1) : d158784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d158784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115320, d158784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12562 q = 1) (hb : d122305 q = 1) : d158786 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d158786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30870 q ha hb
    | true =>
      simp only [d12562, d158786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12563 q = 1) (hb : d122305 q = 1) : d158787 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d158787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12563, d158787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115321 q = 1) (hb : d122305 q = 1) : d158788 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d158788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115321, d158788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115329 q = 1) (hb : d122305 q = 1) : d158798 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d158798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115329, d158798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115330 q = 1) (hb : d122305 q = 1) : d158799 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d158799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115330, d158799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115331 q = 1) (hb : d122305 q = 1) : d158800 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d158800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115331, d158800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30873 (p : Pattern) (ha : d12595 p = 1) (hb : d122305 p = 1) : d124190 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d662 q = 1) : d662 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d415 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d663 q = 1) (hb : d122304 q = 1) : d14370 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d122304, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d663, d122304, d14370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12595 q = 1) (hb : d122305 q = 1) : d124190 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12595, d122305, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12595, d122305, d124190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30874 (p : Pattern) (ha : d12604 p = 1) (hb : d122305 p = 1) : d158806 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d12602 q = 1) : d12602 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12603 q = 1) (hb : d122304 q = 1) : d14155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d122304, d14155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12603, d122304, d14155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12604 q = 1) (hb : d122305 q = 1) : d158806 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12604, d122305, d158806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12604, d122305, d158806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30875 (p : Pattern) (ha : d12610 p = 1) (hb : d122305 p = 1) : d158812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12596 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12596, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30873 q ha hb
    | true =>
      simp only [d12596, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30834 q ha hb
  have h2 (q : Pattern) (ha : d12597 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12597, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12597, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12598 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12598, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12598, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12605 q = 1) (hb : d122305 q = 1) : d158807 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12605, d158807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30834 q ha hb
    | true =>
      simp only [d12605, d158807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30874 q ha hb
  have h5 (q : Pattern) (ha : d12606 q = 1) (hb : d122305 q = 1) : d158808 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12606, d158808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12606, d158808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12607 q = 1) (hb : d122305 q = 1) : d158809 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12607, d158809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12607, d158809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12608 q = 1) (hb : d122305 q = 1) : d158810 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12608, d158810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12608, d158810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12387 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30834 q ha hb
    | true =>
      simp only [d12387, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21904 q ha hb
  have h9 (q : Pattern) (ha : d12388 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12389 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6079 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21904 q ha hb
    | true =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6080 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6081 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12390 q = 1) (hb : d122305 q = 1) : d158677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d158677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12390, d158677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12609 q = 1) (hb : d122305 q = 1) : d158811 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12609, d158811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12609, d158811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12610 q = 1) (hb : d122305 q = 1) : d158812 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12610, d158812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12610, d158812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro30876 (p : Pattern) (ha : d12614 p = 1) (hb : d122305 p = 1) : d158816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30834 q ha hb
    | true =>
      simp only [d12387, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21904 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6079 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21904 q ha hb
    | true =>
      simp only [d6079, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6080 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6081 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12390 q = 1) (hb : d122305 q = 1) : d158677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d158677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12390, d158677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6082 q = 1) (hb : d122305 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6082, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12613 q = 1) (hb : d122305 q = 1) : d158815 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12613, d158815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12613, d158815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12614 q = 1) (hb : d122305 q = 1) : d158816 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12614, d158816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12614, d158816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro30877 (p : Pattern) (ha : d12620 p = 1) (hb : d122305 p = 1) : d158822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12611 q = 1) (hb : d122305 q = 1) : d158813 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12611, d158813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30875 q ha hb
    | true =>
      simp only [d12611, d158813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12612 q = 1) (hb : d122305 q = 1) : d158814 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12612, d158814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12612, d158814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12615 q = 1) (hb : d122305 q = 1) : d158817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30876 q ha hb
    | true =>
      simp only [d12615, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12616 q = 1) (hb : d122305 q = 1) : d158818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12617 q = 1) (hb : d122305 q = 1) : d158819 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12617, d158819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12617, d158819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12618 q = 1) (hb : d122305 q = 1) : d158820 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12618, d158820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12618, d158820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12619 q = 1) (hb : d122305 q = 1) : d158821 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12619, d158821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12619, d158821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12620 q = 1) (hb : d122305 q = 1) : d158822 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12620, d158822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12620, d158822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30878 (p : Pattern) (ha : d12628 p = 1) (hb : d122305 p = 1) : d158826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d122305 q = 1) : d158817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30876 q ha hb
    | true =>
      simp only [d12615, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d122305 q = 1) : d158818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12623 q = 1) (hb : d122305 q = 1) : d124205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30852 q ha hb
    | true =>
      simp only [d12623, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12624 q = 1) (hb : d122305 q = 1) : d124206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12625 q = 1) (hb : d122305 q = 1) : d158823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12625, d158823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12625, d158823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12626 q = 1) (hb : d122305 q = 1) : d158824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12626, d158824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12626, d158824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12627 q = 1) (hb : d122305 q = 1) : d158825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12627, d158825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12627, d158825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12628 q = 1) (hb : d122305 q = 1) : d158826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12628, d158826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12628, d158826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30879 (p : Pattern) (ha : d12657 p = 1) (hb : d122305 p = 1) : d158832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d122305 q = 1) : d158817 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30876 q ha hb
    | true =>
      simp only [d12615, d158817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d122305 q = 1) : d158818 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d158818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12654 q = 1) (hb : d122305 q = 1) : d158829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12654, d158829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12654, d158829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12655 q = 1) (hb : d122305 q = 1) : d158830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12655, d158830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12655, d158830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12656 q = 1) (hb : d122305 q = 1) : d158831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12656, d158831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12656, d158831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12657 q = 1) (hb : d122305 q = 1) : d158832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12657, d158832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12657, d158832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30880 (p : Pattern) (ha : d115341 p = 1) (hb : d122305 p = 1) : d158838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12629 q = 1) (hb : d122305 q = 1) : d158827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12629, d158827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30877 q ha hb
    | true =>
      simp only [d12629, d158827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30878 q ha hb
  have h2 (q : Pattern) (ha : d115337 q = 1) (hb : d122305 q = 1) : d158828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d158828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115337, d158828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12658 q = 1) (hb : d122305 q = 1) : d158833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12658, d158833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30879 q ha hb
    | true =>
      simp only [d12658, d158833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12659 q = 1) (hb : d122305 q = 1) : d158834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12659, d158834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12659, d158834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115338 q = 1) (hb : d122305 q = 1) : d158835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d158835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115338, d158835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115339 q = 1) (hb : d122305 q = 1) : d158836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d158836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115339, d158836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115340 q = 1) (hb : d122305 q = 1) : d158837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d158837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115340, d158837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115341 q = 1) (hb : d122305 q = 1) : d158838 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d158838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115341, d158838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30881 (p : Pattern) (ha : d115347 p = 1) (hb : d122305 p = 1) : d158844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12459 q = 1) (hb : d122305 q = 1) : d158724 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12459, d158724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12459, d158724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30845 q ha hb
  have h2 (q : Pattern) (ha : d12460 q = 1) (hb : d122305 q = 1) : d158725 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12460, d158725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12460, d158725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12469 q = 1) (hb : d122305 q = 1) : d158733 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d158733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30845 q ha hb
    | true =>
      simp only [d12469, d158733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30848 q ha hb
  have h4 (q : Pattern) (ha : d12470 q = 1) (hb : d122305 q = 1) : d158734 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d158734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12470, d158734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12471 q = 1) (hb : d122305 q = 1) : d158735 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12471, d158735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12471, d158735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115325 q = 1) (hb : d122305 q = 1) : d158792 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d158792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30864 q ha hb
    | true =>
      simp only [d115325, d158792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30871 q ha hb
  have h7 (q : Pattern) (ha : d12581 q = 1) (hb : d122305 q = 1) : d158794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12581, d158794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30849 q ha hb
    | true =>
      simp only [d12581, d158794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30850 q ha hb
  have h8 (q : Pattern) (ha : d115326 q = 1) (hb : d122305 q = 1) : d158795 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d158795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115326, d158795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115327 q = 1) (hb : d122305 q = 1) : d158796 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d158796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115327, d158796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115328 q = 1) (hb : d122305 q = 1) : d158797 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d158797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115328, d158797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115332 q = 1) (hb : d122305 q = 1) : d158801 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d158801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115332, d158801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30872 q ha hb
  have h12 (q : Pattern) (ha : d12590 q = 1) (hb : d122305 q = 1) : d124185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12590, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12590, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30851 q ha hb
  have h13 (q : Pattern) (ha : d115333 q = 1) (hb : d122305 q = 1) : d158802 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d158802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115333, d158802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115334 q = 1) (hb : d122305 q = 1) : d158803 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d158803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115334, d158803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115335 q = 1) (hb : d122305 q = 1) : d158804 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d158804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115335, d158804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115336 q = 1) (hb : d122305 q = 1) : d158805 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d158805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115336, d158805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115342 q = 1) (hb : d122305 q = 1) : d158839 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d158839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115342, d158839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30880 q ha hb
  have h18 (q : Pattern) (ha : d12675 q = 1) (hb : d122305 q = 1) : d124234 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12675, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12675, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30854 q ha hb
  have h19 (q : Pattern) (ha : d115343 q = 1) (hb : d122305 q = 1) : d158840 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d158840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115343, d158840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115344 q = 1) (hb : d122305 q = 1) : d158841 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d158841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115344, d158841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115345 q = 1) (hb : d122305 q = 1) : d158842 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d158842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115345, d158842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115346 q = 1) (hb : d122305 q = 1) : d158843 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d158843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115346, d158843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115347 q = 1) (hb : d122305 q = 1) : d158844 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d158844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115347, d158844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30882 (p : Pattern) (ha : d115353 p = 1) (hb : d122305 p = 1) : d158850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115348 q = 1) (hb : d122305 q = 1) : d158845 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d158845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115348, d158845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30881 q ha hb
  have h2 (q : Pattern) (ha : d115349 q = 1) (hb : d122305 q = 1) : d158846 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d158846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115349, d158846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115350 q = 1) (hb : d122305 q = 1) : d158847 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d158847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115350, d158847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115351 q = 1) (hb : d122305 q = 1) : d158848 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d158848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115351, d158848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115352 q = 1) (hb : d122305 q = 1) : d158849 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d158849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115352, d158849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115353 q = 1) (hb : d122305 q = 1) : d158850 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d158850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115353, d158850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30883 (p : Pattern) (ha : d12693 p = 1) (hb : d122305 p = 1) : d158854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12688 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30859 q ha hb
    | true =>
      simp only [d12688, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21930 q ha hb
  have h2 (q : Pattern) (ha : d12689 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12690 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4914 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21930 q ha hb
    | true =>
      simp only [d4914, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4915 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4916 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12691 q = 1) (hb : d122305 q = 1) : d158852 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d158852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12691, d158852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4917 q = 1) (hb : d122305 q = 1) : d124250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4917, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12692 q = 1) (hb : d122305 q = 1) : d158853 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12692, d158853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12692, d158853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12693 q = 1) (hb : d122305 q = 1) : d158854 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12693, d158854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12693, d158854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro30884 (p : Pattern) (ha : d12697 p = 1) (hb : d122305 p = 1) : d124256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4914 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21930 q ha hb
    | true =>
      simp only [d4914, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4915 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4916 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4917 q = 1) (hb : d122305 q = 1) : d124250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4917, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12696 q = 1) (hb : d122305 q = 1) : d124255 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12696, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12696, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12697 q = 1) (hb : d122305 q = 1) : d124256 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12697, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12697, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30885 (p : Pattern) (ha : d12703 p = 1) (hb : d122305 p = 1) : d158860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30883 q ha hb
    | true =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d122305 q = 1) : d158858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d122305 q = 1) : d158859 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d158859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d158859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12703 q = 1) (hb : d122305 q = 1) : d158860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12703, d158860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12703, d158860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30886 (p : Pattern) (ha : d12707 p = 1) (hb : d122305 p = 1) : d124266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d122305 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d122305 q = 1) : d124265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12707 q = 1) (hb : d122305 q = 1) : d124266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12707, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12707, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30887 (p : Pattern) (ha : d12713 p = 1) (hb : d122305 p = 1) : d158866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d122305 q = 1) : d158861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30885 q ha hb
    | true =>
      simp only [d12708, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30886 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d122305 q = 1) : d158862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d122305 q = 1) : d158863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d122305 q = 1) : d158864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d122305 q = 1) : d158865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12713 q = 1) (hb : d122305 q = 1) : d158866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12713, d158866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12713, d158866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30888 (p : Pattern) (ha : d12716 p = 1) (hb : d122305 p = 1) : d158869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30883 q ha hb
    | true =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d122305 q = 1) : d158858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d122305 q = 1) : d158859 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d158859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d158859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12716 q = 1) (hb : d122305 q = 1) : d158869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12716, d158869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12716, d158869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30889 (p : Pattern) (ha : d12717 p = 1) (hb : d122305 p = 1) : d124276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d122305 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d122305 q = 1) : d124265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12717 q = 1) (hb : d122305 q = 1) : d124276 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12717, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12717, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30890 (p : Pattern) (ha : d12723 p = 1) (hb : d122305 p = 1) : d158875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d122305 q = 1) : d158861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30885 q ha hb
    | true =>
      simp only [d12708, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30886 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d122305 q = 1) : d158862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d122305 q = 1) : d158863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d122305 q = 1) : d158864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d122305 q = 1) : d158865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12718 q = 1) (hb : d122305 q = 1) : d158870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d158870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30888 q ha hb
    | true =>
      simp only [d12718, d158870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30889 q ha hb
  have h7 (q : Pattern) (ha : d12719 q = 1) (hb : d122305 q = 1) : d158871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d158871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12720 q = 1) (hb : d122305 q = 1) : d158872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12720, d158872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12721 q = 1) (hb : d122305 q = 1) : d158873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d158873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12722 q = 1) (hb : d122305 q = 1) : d158874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d158874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12723 q = 1) (hb : d122305 q = 1) : d158875 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12723, d158875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12723, d158875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30891 (p : Pattern) (ha : d12833 p = 1) (hb : d122305 p = 1) : d158936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d122305 q = 1) : d158861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30885 q ha hb
    | true =>
      simp only [d12708, d158861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30886 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d122305 q = 1) : d158862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d158862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d122305 q = 1) : d158863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d158863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d122305 q = 1) : d158864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d158864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d122305 q = 1) : d158865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d158865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12828 q = 1) (hb : d122305 q = 1) : d124350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30886 q ha hb
    | true =>
      simp only [d12828, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12829 q = 1) (hb : d122305 q = 1) : d124351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12830 q = 1) (hb : d122305 q = 1) : d124352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12830, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12831 q = 1) (hb : d122305 q = 1) : d124353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12832 q = 1) (hb : d122305 q = 1) : d124354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12833 q = 1) (hb : d122305 q = 1) : d158936 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12833, d158936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12833, d158936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30892 (p : Pattern) (ha : d12839 p = 1) (hb : d122305 p = 1) : d124361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12828 q = 1) (hb : d122305 q = 1) : d124350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30886 q ha hb
    | true =>
      simp only [d12828, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12829 q = 1) (hb : d122305 q = 1) : d124351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12830 q = 1) (hb : d122305 q = 1) : d124352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12830, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12831 q = 1) (hb : d122305 q = 1) : d124353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12832 q = 1) (hb : d122305 q = 1) : d124354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12834 q = 1) (hb : d122305 q = 1) : d124356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30889 q ha hb
    | true =>
      simp only [d12834, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12835 q = 1) (hb : d122305 q = 1) : d124357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12836 q = 1) (hb : d122305 q = 1) : d124358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12836, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12837 q = 1) (hb : d122305 q = 1) : d124359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12838 q = 1) (hb : d122305 q = 1) : d124360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12839 q = 1) (hb : d122305 q = 1) : d124361 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12839, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12839, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30893 (p : Pattern) (ha : d12848 p = 1) (hb : d122305 p = 1) : d124370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12834 q = 1) (hb : d122305 q = 1) : d124356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30889 q ha hb
    | true =>
      simp only [d12834, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12835 q = 1) (hb : d122305 q = 1) : d124357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12836 q = 1) (hb : d122305 q = 1) : d124358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12836, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12837 q = 1) (hb : d122305 q = 1) : d124359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12838 q = 1) (hb : d122305 q = 1) : d124360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12848 q = 1) (hb : d122305 q = 1) : d124370 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12848, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12848, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30894 (p : Pattern) (ha : d12885 p = 1) (hb : d122305 p = 1) : d124398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6211 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21953 q ha hb
    | true =>
      simp only [d6211, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6212 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6213 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6214 q = 1) (hb : d122305 q = 1) : d124388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6214, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12884 q = 1) (hb : d122305 q = 1) : d124397 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12884, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12884, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12885 q = 1) (hb : d122305 q = 1) : d124398 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12885, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12885, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30895 (p : Pattern) (ha : d12935 p = 1) (hb : d122305 p = 1) : d124421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12886 q = 1) (hb : d122305 q = 1) : d124399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30894 q ha hb
    | true =>
      simp only [d12886, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12887 q = 1) (hb : d122305 q = 1) : d124400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12932 q = 1) (hb : d122305 q = 1) : d124418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12932, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12932, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12933 q = 1) (hb : d122305 q = 1) : d124419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12933, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12933, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12934 q = 1) (hb : d122305 q = 1) : d124420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12934, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12934, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12935 q = 1) (hb : d122305 q = 1) : d124421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12935, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12935, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30896 (p : Pattern) (ha : d12941 p = 1) (hb : d122305 p = 1) : d124427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12936 q = 1) (hb : d122305 q = 1) : d124422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12936, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30895 q ha hb
    | true =>
      simp only [d12936, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12937 q = 1) (hb : d122305 q = 1) : d124423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12937, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12937, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12938 q = 1) (hb : d122305 q = 1) : d124424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12938, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12938, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12939 q = 1) (hb : d122305 q = 1) : d124425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12939, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12939, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12940 q = 1) (hb : d122305 q = 1) : d124426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12940, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12940, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12941 q = 1) (hb : d122305 q = 1) : d124427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12941, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12941, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30897 (p : Pattern) (ha : d12728 p = 1) (hb : d122305 p = 1) : d158880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30883 q ha hb
    | true =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d122305 q = 1) : d158858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d122305 q = 1) : d158879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d158879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d158879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12728 q = 1) (hb : d122305 q = 1) : d158880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12728, d158880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12728, d158880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30898 (p : Pattern) (ha : d12730 p = 1) (hb : d122305 p = 1) : d124289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d122305 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d122305 q = 1) : d124288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12730 q = 1) (hb : d122305 q = 1) : d124289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12730, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12730, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30899 (p : Pattern) (ha : d12737 p = 1) (hb : d122305 p = 1) : d158887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30883 q ha hb
    | true =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d122305 q = 1) : d158885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d158885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d158885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d122305 q = 1) : d158886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d158886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d158886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12737 q = 1) (hb : d122305 q = 1) : d158887 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12737, d158887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12737, d158887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30900 (p : Pattern) (ha : d12740 p = 1) (hb : d122305 p = 1) : d124299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d122305 q = 1) : d124297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d122305 q = 1) : d124298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d122305 q = 1) : d124299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12740, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12740, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30901 (p : Pattern) (ha : d12744 p = 1) (hb : d122305 p = 1) : d124303 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d837 q = 1) : d837 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d546 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d838 q = 1) (hb : d122304 q = 1) : d14528 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d838, d122304, d14528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d838, d122304, d14528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12744 q = 1) (hb : d122305 q = 1) : d124303 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12744, d122305, d124303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12744, d122305, d124303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30902 (p : Pattern) (ha : d12751 p = 1) (hb : d122305 p = 1) : d158891 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d12749 q = 1) : d12749 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12750 q = 1) (hb : d122304 q = 1) : d14262 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d122304, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12750, d122304, d14262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12751 q = 1) (hb : d122305 q = 1) : d158891 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12751, d122305, d158891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12751, d122305, d158891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30903 (p : Pattern) (ha : d12757 p = 1) (hb : d122305 p = 1) : d158897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12745 q = 1) (hb : d122305 q = 1) : d124304 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12745, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30901 q ha hb
    | true =>
      simp only [d12745, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30859 q ha hb
  have h2 (q : Pattern) (ha : d12746 q = 1) (hb : d122305 q = 1) : d124305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12746, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12746, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12747 q = 1) (hb : d122305 q = 1) : d124306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12747, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12747, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12752 q = 1) (hb : d122305 q = 1) : d158892 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12752, d158892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30859 q ha hb
    | true =>
      simp only [d12752, d158892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30902 q ha hb
  have h5 (q : Pattern) (ha : d12753 q = 1) (hb : d122305 q = 1) : d158893 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12753, d158893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12753, d158893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12754 q = 1) (hb : d122305 q = 1) : d158894 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12754, d158894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12754, d158894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12755 q = 1) (hb : d122305 q = 1) : d158895 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12755, d158895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12755, d158895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12688 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30859 q ha hb
    | true =>
      simp only [d12688, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21930 q ha hb
  have h9 (q : Pattern) (ha : d12689 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12690 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4914 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21930 q ha hb
    | true =>
      simp only [d4914, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4915 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4916 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12691 q = 1) (hb : d122305 q = 1) : d158852 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d158852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12691, d158852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12756 q = 1) (hb : d122305 q = 1) : d158896 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12756, d158896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12756, d158896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12757 q = 1) (hb : d122305 q = 1) : d158897 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12757, d158897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12757, d158897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro30904 (p : Pattern) (ha : d12763 p = 1) (hb : d122305 p = 1) : d158903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d122305 q = 1) : d158898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d158898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30903 q ha hb
    | true =>
      simp only [d12758, d158898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d122305 q = 1) : d158899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d158899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d158899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30883 q ha hb
    | true =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d122305 q = 1) : d158900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d158900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d158900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d122305 q = 1) : d158901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d158901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d158901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d122305 q = 1) : d158902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d158902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d158902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12763 q = 1) (hb : d122305 q = 1) : d158903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12763, d158903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12763, d158903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30905 (p : Pattern) (ha : d12796 p = 1) (hb : d122305 p = 1) : d158909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30883 q ha hb
    | true =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d122305 q = 1) : d158906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d158906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d158906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d122305 q = 1) : d158907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d158907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d158907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d122305 q = 1) : d158908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d158908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d158908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12796 q = 1) (hb : d122305 q = 1) : d158909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12796, d158909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12796, d158909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30906 (p : Pattern) (ha : d115359 p = 1) (hb : d122305 p = 1) : d158915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d122305 q = 1) : d158881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d158881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30897 q ha hb
    | true =>
      simp only [d12731, d158881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30898 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d122305 q = 1) : d158882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d158882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d158882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d122305 q = 1) : d158883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d158883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d158883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d122305 q = 1) : d158884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d158884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d158884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d122305 q = 1) : d158888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d158888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30899 q ha hb
    | true =>
      simp only [d12741, d158888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30900 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d122305 q = 1) : d158889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d158889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d158889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d122305 q = 1) : d158890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d158890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d158890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d122305 q = 1) : d158904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d158904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30904 q ha hb
    | true =>
      simp only [d12764, d158904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30885 q ha hb
  have h9 (q : Pattern) (ha : d115355 q = 1) (hb : d122305 q = 1) : d158905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d158905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115355, d158905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d122305 q = 1) : d158910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d158910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30905 q ha hb
    | true =>
      simp only [d12797, d158910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d122305 q = 1) : d158911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d158911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d158911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115356 q = 1) (hb : d122305 q = 1) : d158912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d158912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d158912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115357 q = 1) (hb : d122305 q = 1) : d158913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d158913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115357, d158913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115358 q = 1) (hb : d122305 q = 1) : d158914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d158914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115358, d158914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115359 q = 1) (hb : d122305 q = 1) : d158915 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d158915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115359, d158915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30907 (p : Pattern) (ha : d12803 p = 1) (hb : d122305 p = 1) : d158916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30883 q ha hb
    | true =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d122305 q = 1) : d158858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d158858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d122305 q = 1) : d158879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d158879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d158879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12803 q = 1) (hb : d122305 q = 1) : d158916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12803, d158916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12803, d158916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30908 (p : Pattern) (ha : d12804 p = 1) (hb : d122305 p = 1) : d124329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d122305 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d122305 q = 1) : d124288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12804 q = 1) (hb : d122305 q = 1) : d124329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12804, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12804, d124329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30909 (p : Pattern) (ha : d12809 p = 1) (hb : d122305 p = 1) : d158921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30883 q ha hb
    | true =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d122305 q = 1) : d158857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d158857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d122305 q = 1) : d158885 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d158885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d158885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d122305 q = 1) : d158886 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d158886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d158886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12809 q = 1) (hb : d122305 q = 1) : d158921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12809, d158921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12809, d158921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30910 (p : Pattern) (ha : d12810 p = 1) (hb : d122305 p = 1) : d124335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d122305 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30884 q ha hb
    | true =>
      simp only [d12698, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d122305 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d122305 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d122305 q = 1) : d124297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d122305 q = 1) : d124298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12810 q = 1) (hb : d122305 q = 1) : d124335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12810, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12810, d124335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30911 (p : Pattern) (ha : d12814 p = 1) (hb : d122305 p = 1) : d158925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d122305 q = 1) : d158898 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d158898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30903 q ha hb
    | true =>
      simp only [d12758, d158898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d122305 q = 1) : d158899 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d158899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d158899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30883 q ha hb
    | true =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d122305 q = 1) : d158900 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d158900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d158900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d122305 q = 1) : d158901 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d158901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d158901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d122305 q = 1) : d158902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d158902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d158902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12814 q = 1) (hb : d122305 q = 1) : d158925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12814, d158925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12814, d158925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30912 (p : Pattern) (ha : d12820 p = 1) (hb : d122305 p = 1) : d158928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d122305 q = 1) : d158855 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30883 q ha hb
    | true =>
      simp only [d12694, d158855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d122305 q = 1) : d158856 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d158856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d122305 q = 1) : d158906 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d158906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d158906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d122305 q = 1) : d158907 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d158907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d158907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d122305 q = 1) : d158908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d158908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d158908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12820 q = 1) (hb : d122305 q = 1) : d158928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12820, d158928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12820, d158928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30913 (p : Pattern) (ha : d115364 p = 1) (hb : d122305 p = 1) : d158934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d122305 q = 1) : d158881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d158881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30897 q ha hb
    | true =>
      simp only [d12731, d158881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30898 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d122305 q = 1) : d158882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d158882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d158882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d122305 q = 1) : d158883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d158883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d158883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d122305 q = 1) : d158884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d158884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d158884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d122305 q = 1) : d158888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d158888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30899 q ha hb
    | true =>
      simp only [d12741, d158888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30900 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d122305 q = 1) : d158889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d158889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d158889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d122305 q = 1) : d158890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d158890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d158890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d122305 q = 1) : d158904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d158904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30904 q ha hb
    | true =>
      simp only [d12764, d158904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30885 q ha hb
  have h9 (q : Pattern) (ha : d115355 q = 1) (hb : d122305 q = 1) : d158905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d158905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115355, d158905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d122305 q = 1) : d158910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d158910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30905 q ha hb
    | true =>
      simp only [d12797, d158910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d122305 q = 1) : d158911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d158911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d158911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115356 q = 1) (hb : d122305 q = 1) : d158912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d158912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d158912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115357 q = 1) (hb : d122305 q = 1) : d158913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d158913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115357, d158913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115358 q = 1) (hb : d122305 q = 1) : d158914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d158914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115358, d158914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12805 q = 1) (hb : d122305 q = 1) : d158917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12805, d158917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30907 q ha hb
    | true =>
      simp only [d12805, d158917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30908 q ha hb
  have h16 (q : Pattern) (ha : d12806 q = 1) (hb : d122305 q = 1) : d158918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12806, d158918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12806, d158918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12807 q = 1) (hb : d122305 q = 1) : d158919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12807, d158919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12807, d158919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12808 q = 1) (hb : d122305 q = 1) : d158920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12808, d158920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12808, d158920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12811 q = 1) (hb : d122305 q = 1) : d158922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12811, d158922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30909 q ha hb
    | true =>
      simp only [d12811, d158922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30910 q ha hb
  have h20 (q : Pattern) (ha : d12812 q = 1) (hb : d122305 q = 1) : d158923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12812, d158923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12812, d158923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12813 q = 1) (hb : d122305 q = 1) : d158924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12813, d158924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12813, d158924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12815 q = 1) (hb : d122305 q = 1) : d158926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d158926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30911 q ha hb
    | true =>
      simp only [d12815, d158926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30888 q ha hb
  have h23 (q : Pattern) (ha : d115360 q = 1) (hb : d122305 q = 1) : d158927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d158927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115360, d158927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12821 q = 1) (hb : d122305 q = 1) : d158929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d158929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30912 q ha hb
    | true =>
      simp only [d12821, d158929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12822 q = 1) (hb : d122305 q = 1) : d158930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d158930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12822, d158930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115361 q = 1) (hb : d122305 q = 1) : d158931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d158931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115361, d158931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115362 q = 1) (hb : d122305 q = 1) : d158932 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d158932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115362, d158932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115363 q = 1) (hb : d122305 q = 1) : d158933 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d158933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115363, d158933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115364 q = 1) (hb : d122305 q = 1) : d158934 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d158934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115364, d158934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro30914 (p : Pattern) (ha : d115371 p = 1) (hb : d122305 p = 1) : d158943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12815 q = 1) (hb : d122305 q = 1) : d158926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d158926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30911 q ha hb
    | true =>
      simp only [d12815, d158926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30888 q ha hb
  have h2 (q : Pattern) (ha : d115360 q = 1) (hb : d122305 q = 1) : d158927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d158927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115360, d158927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12821 q = 1) (hb : d122305 q = 1) : d158929 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d158929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30912 q ha hb
    | true =>
      simp only [d12821, d158929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12822 q = 1) (hb : d122305 q = 1) : d158930 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d158930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12822, d158930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115361 q = 1) (hb : d122305 q = 1) : d158931 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d158931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115361, d158931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115369 q = 1) (hb : d122305 q = 1) : d158941 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d158941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115369, d158941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115370 q = 1) (hb : d122305 q = 1) : d158942 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d158942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115370, d158942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115371 q = 1) (hb : d122305 q = 1) : d158943 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d158943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115371, d158943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30915 (p : Pattern) (ha : d12854 p = 1) (hb : d122305 p = 1) : d124376 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d968 q = 1) : d968 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d969 q = 1) (hb : d122304 q = 1) : d14643 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d969, d122304, d14643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d969, d122304, d14643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12854 q = 1) (hb : d122305 q = 1) : d124376 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12854, d122305, d124376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12854, d122305, d124376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30916 (p : Pattern) (ha : d12863 p = 1) (hb : d122305 p = 1) : d158949 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d12861 q = 1) : d12861 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12862 q = 1) (hb : d122304 q = 1) : d14371 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d122304, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12862, d122304, d14371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12863 q = 1) (hb : d122305 q = 1) : d158949 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12863, d122305, d158949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12863, d122305, d158949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30917 (p : Pattern) (ha : d12873 p = 1) (hb : d122305 p = 1) : d158956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12855 q = 1) (hb : d122305 q = 1) : d124377 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12855, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30915 q ha hb
    | true =>
      simp only [d12855, d124377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30873 q ha hb
  have h2 (q : Pattern) (ha : d12856 q = 1) (hb : d122305 q = 1) : d124378 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12856, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12856, d124378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12857 q = 1) (hb : d122305 q = 1) : d124379 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12857, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12857, d124379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12864 q = 1) (hb : d122305 q = 1) : d158950 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12864, d158950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30873 q ha hb
    | true =>
      simp only [d12864, d158950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30916 q ha hb
  have h5 (q : Pattern) (ha : d12865 q = 1) (hb : d122305 q = 1) : d158951 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12865, d158951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12865, d158951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12866 q = 1) (hb : d122305 q = 1) : d158952 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12866, d158952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12866, d158952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12867 q = 1) (hb : d122305 q = 1) : d158953 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12867, d158953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12867, d158953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12868 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30873 q ha hb
    | true =>
      simp only [d12868, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21953 q ha hb
  have h9 (q : Pattern) (ha : d12869 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12870 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6211 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21953 q ha hb
    | true =>
      simp only [d6211, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6212 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6213 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12871 q = 1) (hb : d122305 q = 1) : d158954 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d158954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12871, d158954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12872 q = 1) (hb : d122305 q = 1) : d158955 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12872, d158955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12872, d158955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12873 q = 1) (hb : d122305 q = 1) : d158956 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12873, d158956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12873, d158956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro30918 (p : Pattern) (ha : d12877 p = 1) (hb : d122305 p = 1) : d158960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12868 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30873 q ha hb
    | true =>
      simp only [d12868, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21953 q ha hb
  have h2 (q : Pattern) (ha : d12869 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12870 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6211 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21953 q ha hb
    | true =>
      simp only [d6211, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6212 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6213 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12871 q = 1) (hb : d122305 q = 1) : d158954 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d158954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12871, d158954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6214 q = 1) (hb : d122305 q = 1) : d124388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6214, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12876 q = 1) (hb : d122305 q = 1) : d158959 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12876, d158959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12876, d158959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12877 q = 1) (hb : d122305 q = 1) : d158960 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12877, d158960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12877, d158960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro30919 (p : Pattern) (ha : d12883 p = 1) (hb : d122305 p = 1) : d158966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12874 q = 1) (hb : d122305 q = 1) : d158957 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12874, d158957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30917 q ha hb
    | true =>
      simp only [d12874, d158957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12875 q = 1) (hb : d122305 q = 1) : d158958 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12875, d158958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12875, d158958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12878 q = 1) (hb : d122305 q = 1) : d158961 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30918 q ha hb
    | true =>
      simp only [d12878, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12879 q = 1) (hb : d122305 q = 1) : d158962 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12880 q = 1) (hb : d122305 q = 1) : d158963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12880, d158963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12880, d158963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12881 q = 1) (hb : d122305 q = 1) : d158964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12881, d158964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12881, d158964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12882 q = 1) (hb : d122305 q = 1) : d158965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12882, d158965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12882, d158965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12883 q = 1) (hb : d122305 q = 1) : d158966 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12883, d158966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12883, d158966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30920 (p : Pattern) (ha : d12891 p = 1) (hb : d122305 p = 1) : d158970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d122305 q = 1) : d158961 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30918 q ha hb
    | true =>
      simp only [d12878, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d122305 q = 1) : d158962 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12886 q = 1) (hb : d122305 q = 1) : d124399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30894 q ha hb
    | true =>
      simp only [d12886, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12887 q = 1) (hb : d122305 q = 1) : d124400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12888 q = 1) (hb : d122305 q = 1) : d158967 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12888, d158967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12888, d158967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12889 q = 1) (hb : d122305 q = 1) : d158968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12889, d158968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12889, d158968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12890 q = 1) (hb : d122305 q = 1) : d158969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12890, d158969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12890, d158969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12891 q = 1) (hb : d122305 q = 1) : d158970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12891, d158970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12891, d158970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30921 (p : Pattern) (ha : d12924 p = 1) (hb : d122305 p = 1) : d158976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d122305 q = 1) : d158961 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30918 q ha hb
    | true =>
      simp only [d12878, d158961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d122305 q = 1) : d158962 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d158962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12921 q = 1) (hb : d122305 q = 1) : d158973 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12921, d158973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12921, d158973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12922 q = 1) (hb : d122305 q = 1) : d158974 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12922, d158974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12922, d158974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12923 q = 1) (hb : d122305 q = 1) : d158975 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12923, d158975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12923, d158975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12924 q = 1) (hb : d122305 q = 1) : d158976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12924, d158976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12924, d158976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30922 (p : Pattern) (ha : d115381 p = 1) (hb : d122305 p = 1) : d158982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12892 q = 1) (hb : d122305 q = 1) : d158971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12892, d158971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30919 q ha hb
    | true =>
      simp only [d12892, d158971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30920 q ha hb
  have h2 (q : Pattern) (ha : d115377 q = 1) (hb : d122305 q = 1) : d158972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d158972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115377, d158972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12925 q = 1) (hb : d122305 q = 1) : d158977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12925, d158977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30921 q ha hb
    | true =>
      simp only [d12925, d158977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12926 q = 1) (hb : d122305 q = 1) : d158978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12926, d158978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12926, d158978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115378 q = 1) (hb : d122305 q = 1) : d158979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d158979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115378, d158979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115379 q = 1) (hb : d122305 q = 1) : d158980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d158980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115379, d158980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115380 q = 1) (hb : d122305 q = 1) : d158981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d158981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115380, d158981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115381 q = 1) (hb : d122305 q = 1) : d158982 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d158982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115381, d158982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30923 (p : Pattern) (ha : d115387 p = 1) (hb : d122305 p = 1) : d158988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12714 q = 1) (hb : d122305 q = 1) : d158867 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12714, d158867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12714, d158867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30887 q ha hb
  have h2 (q : Pattern) (ha : d12715 q = 1) (hb : d122305 q = 1) : d158868 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12715, d158868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12715, d158868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12724 q = 1) (hb : d122305 q = 1) : d158876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d158876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30887 q ha hb
    | true =>
      simp only [d12724, d158876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30890 q ha hb
  have h4 (q : Pattern) (ha : d12725 q = 1) (hb : d122305 q = 1) : d158877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d158877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12725, d158877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12726 q = 1) (hb : d122305 q = 1) : d158878 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12726, d158878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12726, d158878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115365 q = 1) (hb : d122305 q = 1) : d158935 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d158935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30906 q ha hb
    | true =>
      simp only [d115365, d158935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30913 q ha hb
  have h7 (q : Pattern) (ha : d12840 q = 1) (hb : d122305 q = 1) : d158937 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12840, d158937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30891 q ha hb
    | true =>
      simp only [d12840, d158937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30892 q ha hb
  have h8 (q : Pattern) (ha : d115366 q = 1) (hb : d122305 q = 1) : d158938 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d158938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115366, d158938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115367 q = 1) (hb : d122305 q = 1) : d158939 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d158939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115367, d158939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115368 q = 1) (hb : d122305 q = 1) : d158940 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d158940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115368, d158940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115372 q = 1) (hb : d122305 q = 1) : d158944 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d158944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115372, d158944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30914 q ha hb
  have h12 (q : Pattern) (ha : d12849 q = 1) (hb : d122305 q = 1) : d124371 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12849, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12849, d124371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30893 q ha hb
  have h13 (q : Pattern) (ha : d115373 q = 1) (hb : d122305 q = 1) : d158945 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d158945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115373, d158945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115374 q = 1) (hb : d122305 q = 1) : d158946 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d158946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115374, d158946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115375 q = 1) (hb : d122305 q = 1) : d158947 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d158947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115375, d158947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115376 q = 1) (hb : d122305 q = 1) : d158948 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d158948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115376, d158948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115382 q = 1) (hb : d122305 q = 1) : d158983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d158983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115382, d158983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30922 q ha hb
  have h18 (q : Pattern) (ha : d12942 q = 1) (hb : d122305 q = 1) : d124428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12942, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12942, d124428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30896 q ha hb
  have h19 (q : Pattern) (ha : d115383 q = 1) (hb : d122305 q = 1) : d158984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d158984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115383, d158984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115384 q = 1) (hb : d122305 q = 1) : d158985 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d158985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115384, d158985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115385 q = 1) (hb : d122305 q = 1) : d158986 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d158986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115385, d158986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115386 q = 1) (hb : d122305 q = 1) : d158987 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d158987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115386, d158987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115387 q = 1) (hb : d122305 q = 1) : d158988 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d158988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115387, d158988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30924 (p : Pattern) (ha : d115393 p = 1) (hb : d122305 p = 1) : d158994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115388 q = 1) (hb : d122305 q = 1) : d158989 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d158989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115388, d158989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30923 q ha hb
  have h2 (q : Pattern) (ha : d115389 q = 1) (hb : d122305 q = 1) : d158990 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d158990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115389, d158990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115390 q = 1) (hb : d122305 q = 1) : d158991 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d158991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115390, d158991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115391 q = 1) (hb : d122305 q = 1) : d158992 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d158992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115391, d158992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115392 q = 1) (hb : d122305 q = 1) : d158993 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d158993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115392, d158993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115393 q = 1) (hb : d122305 q = 1) : d158994 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d158994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115393, d158994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30925 (p : Pattern) (ha : d12956 p = 1) (hb : d122305 p = 1) : d124442 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1103 q = 1) : d1103 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1113 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1114 q = 1) (hb : d122304 q = 1) : d14757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d122304, d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1114, d122304, d14757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12956 q = 1) (hb : d122305 q = 1) : d124442 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12956, d122305, d124442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12956, d122305, d124442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30926 (p : Pattern) (ha : d12967 p = 1) (hb : d122305 p = 1) : d158999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30925 q ha hb
    | true =>
      simp only [d12957, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21982 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5023 q = 1) (hb : d122305 q = 1) : d5023 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5024 q = 1) (hb : d122305 q = 1) : d124513 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21982 q ha hb
    | true =>
      simp only [d5024, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5025 q = 1) (hb : d122305 q = 1) : d124514 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5026 q = 1) (hb : d122305 q = 1) : d124515 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12960 q = 1) (hb : d122305 q = 1) : d158997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12961 q = 1) (hb : d122305 q = 1) : d12961 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d12962 q = 1) (hb : d122305 q = 1) : d124448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21982 q ha hb
    | true =>
      simp only [d12962, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12963 q = 1) (hb : d122305 q = 1) : d124449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12964 q = 1) (hb : d122305 q = 1) : d124450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12965 q = 1) (hb : d122305 q = 1) : d124451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12965, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d12966 q = 1) (hb : d122305 q = 1) : d158998 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12966, d158998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12966, d158998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12967 q = 1) (hb : d122305 q = 1) : d158999 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12967, d158999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12967, d158999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro30927 (p : Pattern) (ha : d12971 p = 1) (hb : d122305 p = 1) : d124457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12961 q = 1) (hb : d122305 q = 1) : d12961 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12962 q = 1) (hb : d122305 q = 1) : d124448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21982 q ha hb
    | true =>
      simp only [d12962, d124448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12963 q = 1) (hb : d122305 q = 1) : d124449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d124449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12964 q = 1) (hb : d122305 q = 1) : d124450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d124450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12965 q = 1) (hb : d122305 q = 1) : d124451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12965, d124451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12970 q = 1) (hb : d122305 q = 1) : d124456 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12970, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12970, d124456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12971 q = 1) (hb : d122305 q = 1) : d124457 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12971, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12971, d124457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30928 (p : Pattern) (ha : d12977 p = 1) (hb : d122305 p = 1) : d159005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30926 q ha hb
    | true =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d122305 q = 1) : d159003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d122305 q = 1) : d159004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d159004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d159004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12977 q = 1) (hb : d122305 q = 1) : d159005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12977, d159005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12977, d159005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30929 (p : Pattern) (ha : d12981 p = 1) (hb : d122305 p = 1) : d124467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d122305 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d122305 q = 1) : d124466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12981 q = 1) (hb : d122305 q = 1) : d124467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12981, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12981, d124467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30930 (p : Pattern) (ha : d12987 p = 1) (hb : d122305 p = 1) : d159011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d122305 q = 1) : d159006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30928 q ha hb
    | true =>
      simp only [d12982, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30929 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d122305 q = 1) : d159007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d122305 q = 1) : d159008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d122305 q = 1) : d159009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d122305 q = 1) : d159010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12987 q = 1) (hb : d122305 q = 1) : d159011 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12987, d159011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12987, d159011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30931 (p : Pattern) (ha : d12990 p = 1) (hb : d122305 p = 1) : d159014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30926 q ha hb
    | true =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d122305 q = 1) : d159003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d122305 q = 1) : d159004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d159004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d159004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12990 q = 1) (hb : d122305 q = 1) : d159014 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12990, d159014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12990, d159014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30932 (p : Pattern) (ha : d12991 p = 1) (hb : d122305 p = 1) : d124477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d122305 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d122305 q = 1) : d124466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d124466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12991 q = 1) (hb : d122305 q = 1) : d124477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12991, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12991, d124477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30933 (p : Pattern) (ha : d12997 p = 1) (hb : d122305 p = 1) : d159020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d122305 q = 1) : d159006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30928 q ha hb
    | true =>
      simp only [d12982, d159006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30929 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d122305 q = 1) : d159007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d159007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d122305 q = 1) : d159008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d159008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d122305 q = 1) : d159009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d159009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d122305 q = 1) : d159010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d159010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12992 q = 1) (hb : d122305 q = 1) : d159015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d159015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30931 q ha hb
    | true =>
      simp only [d12992, d159015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30932 q ha hb
  have h7 (q : Pattern) (ha : d12993 q = 1) (hb : d122305 q = 1) : d159016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d159016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12994 q = 1) (hb : d122305 q = 1) : d159017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12994, d159017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12995 q = 1) (hb : d122305 q = 1) : d159018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d159018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12996 q = 1) (hb : d122305 q = 1) : d159019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d159019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12997 q = 1) (hb : d122305 q = 1) : d159020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12997, d159020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12997, d159020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30934 (p : Pattern) (ha : d13040 p = 1) (hb : d122305 p = 1) : d159046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30925 q ha hb
    | true =>
      simp only [d12957, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21982 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5023 q = 1) (hb : d122305 q = 1) : d5023 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5024 q = 1) (hb : d122305 q = 1) : d124513 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21982 q ha hb
    | true =>
      simp only [d5024, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5025 q = 1) (hb : d122305 q = 1) : d124514 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5026 q = 1) (hb : d122305 q = 1) : d124515 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12960 q = 1) (hb : d122305 q = 1) : d158997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5027 q = 1) (hb : d122305 q = 1) : d124516 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5027, d124516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13039 q = 1) (hb : d122305 q = 1) : d159045 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13039, d159045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13039, d159045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13040 q = 1) (hb : d122305 q = 1) : d159046 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13040, d159046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13040, d159046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro30935 (p : Pattern) (ha : d13050 p = 1) (hb : d122305 p = 1) : d159056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d122305 q = 1) : d159047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30934 q ha hb
    | true =>
      simp only [d13041, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d122305 q = 1) : d159048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d122305 q = 1) : d159053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d159053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d159053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d122305 q = 1) : d159054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d159054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d159054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d122305 q = 1) : d159055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d159055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d159055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13050 q = 1) (hb : d122305 q = 1) : d159056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13050, d159056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13050, d159056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30936 (p : Pattern) (ha : d13134 p = 1) (hb : d122305 p = 1) : d159095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13124 q = 1) (hb : d122305 q = 1) : d159090 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13124, d159090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30935 q ha hb
    | true =>
      simp only [d13124, d159090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30929 q ha hb
  have h2 (q : Pattern) (ha : d13125 q = 1) (hb : d122305 q = 1) : d159091 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13125, d159091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13125, d159091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13126 q = 1) (hb : d122305 q = 1) : d159092 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13126, d159092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13126, d159092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13127 q = 1) (hb : d122305 q = 1) : d159093 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13127, d159093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13127, d159093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13128 q = 1) (hb : d122305 q = 1) : d159094 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13128, d159094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13128, d159094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13129 q = 1) (hb : d122305 q = 1) : d124569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30929 q ha hb
    | true =>
      simp only [d13129, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13130 q = 1) (hb : d122305 q = 1) : d124570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13131 q = 1) (hb : d122305 q = 1) : d124571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13131, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13132 q = 1) (hb : d122305 q = 1) : d124572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13133 q = 1) (hb : d122305 q = 1) : d124573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13134 q = 1) (hb : d122305 q = 1) : d159095 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13134, d159095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13134, d159095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30937 (p : Pattern) (ha : d13140 p = 1) (hb : d122305 p = 1) : d124580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13129 q = 1) (hb : d122305 q = 1) : d124569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30929 q ha hb
    | true =>
      simp only [d13129, d124569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13130 q = 1) (hb : d122305 q = 1) : d124570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d124570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13131 q = 1) (hb : d122305 q = 1) : d124571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13131, d124571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13132 q = 1) (hb : d122305 q = 1) : d124572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d124572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13133 q = 1) (hb : d122305 q = 1) : d124573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d124573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13135 q = 1) (hb : d122305 q = 1) : d124575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30932 q ha hb
    | true =>
      simp only [d13135, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13136 q = 1) (hb : d122305 q = 1) : d124576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13137 q = 1) (hb : d122305 q = 1) : d124577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13137, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13138 q = 1) (hb : d122305 q = 1) : d124578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13139 q = 1) (hb : d122305 q = 1) : d124579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13140 q = 1) (hb : d122305 q = 1) : d124580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13140, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13140, d124580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30938 (p : Pattern) (ha : d13149 p = 1) (hb : d122305 p = 1) : d124589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13135 q = 1) (hb : d122305 q = 1) : d124575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30932 q ha hb
    | true =>
      simp only [d13135, d124575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13136 q = 1) (hb : d122305 q = 1) : d124576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d124576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13137 q = 1) (hb : d122305 q = 1) : d124577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13137, d124577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13138 q = 1) (hb : d122305 q = 1) : d124578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d124578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13139 q = 1) (hb : d122305 q = 1) : d124579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d124579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13149 q = 1) (hb : d122305 q = 1) : d124589 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13149, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13149, d124589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30939 (p : Pattern) (ha : d13196 p = 1) (hb : d122305 p = 1) : d124627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13190 q = 1) (hb : d122305 q = 1) : d13190 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13191 q = 1) (hb : d122305 q = 1) : d124622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22005 q ha hb
    | true =>
      simp only [d13191, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13192 q = 1) (hb : d122305 q = 1) : d124623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13193 q = 1) (hb : d122305 q = 1) : d124624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13194 q = 1) (hb : d122305 q = 1) : d124625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13194, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13195 q = 1) (hb : d122305 q = 1) : d124626 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13195, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13195, d124626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13196 q = 1) (hb : d122305 q = 1) : d124627 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13196, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13196, d124627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30940 (p : Pattern) (ha : d13260 p = 1) (hb : d122305 p = 1) : d124654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13197 q = 1) (hb : d122305 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30939 q ha hb
    | true =>
      simp only [d13197, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13198 q = 1) (hb : d122305 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13257 q = 1) (hb : d122305 q = 1) : d124651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13257, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13257, d124651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13258 q = 1) (hb : d122305 q = 1) : d124652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13258, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13258, d124652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13259 q = 1) (hb : d122305 q = 1) : d124653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13259, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13259, d124653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13260 q = 1) (hb : d122305 q = 1) : d124654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13260, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13260, d124654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30941 (p : Pattern) (ha : d13266 p = 1) (hb : d122305 p = 1) : d124660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13261 q = 1) (hb : d122305 q = 1) : d124655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13261, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30940 q ha hb
    | true =>
      simp only [d13261, d124655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13262 q = 1) (hb : d122305 q = 1) : d124656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13262, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13262, d124656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13263 q = 1) (hb : d122305 q = 1) : d124657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13263, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13263, d124657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13264 q = 1) (hb : d122305 q = 1) : d124658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13264, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13264, d124658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13265 q = 1) (hb : d122305 q = 1) : d124659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13265, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13265, d124659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13266 q = 1) (hb : d122305 q = 1) : d124660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13266, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13266, d124660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30942 (p : Pattern) (ha : d13002 p = 1) (hb : d122305 p = 1) : d159025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30926 q ha hb
    | true =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d122305 q = 1) : d159003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d122305 q = 1) : d159024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d159024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d159024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13002 q = 1) (hb : d122305 q = 1) : d159025 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13002, d159025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13002, d159025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30943 (p : Pattern) (ha : d13004 p = 1) (hb : d122305 p = 1) : d124490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d122305 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d122305 q = 1) : d124489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13004 q = 1) (hb : d122305 q = 1) : d124490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13004, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13004, d124490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30944 (p : Pattern) (ha : d13011 p = 1) (hb : d122305 p = 1) : d159032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30926 q ha hb
    | true =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d122305 q = 1) : d159030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d159030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d159030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d122305 q = 1) : d159031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d159031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d159031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13011 q = 1) (hb : d122305 q = 1) : d159032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13011, d159032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13011, d159032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30945 (p : Pattern) (ha : d13014 p = 1) (hb : d122305 p = 1) : d124500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d122305 q = 1) : d124498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d122305 q = 1) : d124499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d122305 q = 1) : d124500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13014, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13014, d124500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30946 (p : Pattern) (ha : d13018 p = 1) (hb : d122305 p = 1) : d124504 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1213 q = 1) : d1213 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1103 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1214 q = 1) (hb : d122304 q = 1) : d14835 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1214, d122304, d14835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1214, d122304, d14835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13018 q = 1) (hb : d122305 q = 1) : d124504 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13018, d122305, d124504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13018, d122305, d124504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30947 (p : Pattern) (ha : d13030 p = 1) (hb : d122305 p = 1) : d159036 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13023 q = 1) : d13023 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13028 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13029 q = 1) (hb : d122304 q = 1) : d14843 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13029, d122304, d14843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13029, d122304, d14843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13030 q = 1) (hb : d122305 q = 1) : d159036 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13030, d122305, d159036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13030, d122305, d159036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30948 (p : Pattern) (ha : d13036 p = 1) (hb : d122305 p = 1) : d159042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13019 q = 1) (hb : d122305 q = 1) : d124505 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13019, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30946 q ha hb
    | true =>
      simp only [d13019, d124505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30925 q ha hb
  have h2 (q : Pattern) (ha : d13020 q = 1) (hb : d122305 q = 1) : d124506 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13020, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13020, d124506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13021 q = 1) (hb : d122305 q = 1) : d124507 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13021, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13021, d124507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13031 q = 1) (hb : d122305 q = 1) : d159037 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13031, d159037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30925 q ha hb
    | true =>
      simp only [d13031, d159037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30947 q ha hb
  have h5 (q : Pattern) (ha : d13032 q = 1) (hb : d122305 q = 1) : d159038 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13032, d159038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13032, d159038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13033 q = 1) (hb : d122305 q = 1) : d159039 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13033, d159039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13033, d159039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13034 q = 1) (hb : d122305 q = 1) : d159040 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13034, d159040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13034, d159040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12957 q = 1) (hb : d122305 q = 1) : d124444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30925 q ha hb
    | true =>
      simp only [d12957, d124444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21982 q ha hb
  have h9 (q : Pattern) (ha : d12958 q = 1) (hb : d122305 q = 1) : d124445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d124445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12959 q = 1) (hb : d122305 q = 1) : d124446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d124446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5023 q = 1) (hb : d122305 q = 1) : d5023 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5024 q = 1) (hb : d122305 q = 1) : d124513 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro21982 q ha hb
    | true =>
      simp only [d5024, d124513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5025 q = 1) (hb : d122305 q = 1) : d124514 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d124514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5026 q = 1) (hb : d122305 q = 1) : d124515 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d124515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12960 q = 1) (hb : d122305 q = 1) : d158997 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12960, d158997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13035 q = 1) (hb : d122305 q = 1) : d159041 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13035, d159041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13035, d159041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13036 q = 1) (hb : d122305 q = 1) : d159042 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13036, d159042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13036, d159042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro30949 (p : Pattern) (ha : d13046 p = 1) (hb : d122305 p = 1) : d159052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d122305 q = 1) : d159043 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d159043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30948 q ha hb
    | true =>
      simp only [d13037, d159043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d122305 q = 1) : d159044 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d159044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d159044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d122305 q = 1) : d159047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30934 q ha hb
    | true =>
      simp only [d13041, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d122305 q = 1) : d159048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d122305 q = 1) : d159049 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d159049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d159049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d122305 q = 1) : d159050 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d159050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d159050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d122305 q = 1) : d159051 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d159051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d159051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13046 q = 1) (hb : d122305 q = 1) : d159052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13046, d159052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13046, d159052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30950 (p : Pattern) (ha : d13091 p = 1) (hb : d122305 p = 1) : d159062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30926 q ha hb
    | true =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d122305 q = 1) : d159059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d159059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d159059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d122305 q = 1) : d159060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d159060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d159060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d122305 q = 1) : d159061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d159061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d159061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13091 q = 1) (hb : d122305 q = 1) : d159062 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13091, d159062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13091, d159062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30951 (p : Pattern) (ha : d115400 p = 1) (hb : d122305 p = 1) : d159068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d122305 q = 1) : d159026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d159026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30942 q ha hb
    | true =>
      simp only [d13005, d159026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30943 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d122305 q = 1) : d159027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d159027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d159027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d122305 q = 1) : d159028 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d159028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d159028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d122305 q = 1) : d159029 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d159029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d159029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d122305 q = 1) : d159033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d159033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30944 q ha hb
    | true =>
      simp only [d13015, d159033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30945 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d122305 q = 1) : d159034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d159034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d159034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d122305 q = 1) : d159035 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d159035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d159035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d122305 q = 1) : d159057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d159057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30949 q ha hb
    | true =>
      simp only [d13051, d159057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30935 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d122305 q = 1) : d159058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d159058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d159058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d122305 q = 1) : d159063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d159063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30950 q ha hb
    | true =>
      simp only [d13092, d159063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d122305 q = 1) : d159064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d159064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d159064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d122305 q = 1) : d159065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d159065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d159065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d122305 q = 1) : d159066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d159066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d159066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d122305 q = 1) : d159067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d159067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d159067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115400 q = 1) (hb : d122305 q = 1) : d159068 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d159068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115400, d159068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30952 (p : Pattern) (ha : d13098 p = 1) (hb : d122305 p = 1) : d159069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30926 q ha hb
    | true =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d122305 q = 1) : d159003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d159003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d122305 q = 1) : d159024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d159024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d159024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13098 q = 1) (hb : d122305 q = 1) : d159069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13098, d159069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13098, d159069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30953 (p : Pattern) (ha : d13099 p = 1) (hb : d122305 p = 1) : d124542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d122305 q = 1) : d124465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d124465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d122305 q = 1) : d124489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d124489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13099 q = 1) (hb : d122305 q = 1) : d124542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13099, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13099, d124542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30954 (p : Pattern) (ha : d13104 p = 1) (hb : d122305 p = 1) : d159074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30926 q ha hb
    | true =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d122305 q = 1) : d159002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d159002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d122305 q = 1) : d159030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d159030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d159030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d122305 q = 1) : d159031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d159031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d159031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13104 q = 1) (hb : d122305 q = 1) : d159074 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13104, d159074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13104, d159074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30955 (p : Pattern) (ha : d13105 p = 1) (hb : d122305 p = 1) : d124548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d122305 q = 1) : d124464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d124464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d122305 q = 1) : d124498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d124498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d122305 q = 1) : d124499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d124499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13105 q = 1) (hb : d122305 q = 1) : d124548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13105, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13105, d124548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30956 (p : Pattern) (ha : d13109 p = 1) (hb : d122305 p = 1) : d159078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d122305 q = 1) : d159043 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d159043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30948 q ha hb
    | true =>
      simp only [d13037, d159043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d122305 q = 1) : d159044 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d159044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d159044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d122305 q = 1) : d159047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30934 q ha hb
    | true =>
      simp only [d13041, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d122305 q = 1) : d159048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d122305 q = 1) : d159049 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d159049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d159049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d122305 q = 1) : d159050 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d159050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d159050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d122305 q = 1) : d159051 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d159051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d159051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13109 q = 1) (hb : d122305 q = 1) : d159078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13109, d159078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13109, d159078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30957 (p : Pattern) (ha : d13110 p = 1) (hb : d122305 p = 1) : d159079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d122305 q = 1) : d159047 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30934 q ha hb
    | true =>
      simp only [d13041, d159047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d122305 q = 1) : d159048 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d159048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d122305 q = 1) : d124458 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30927 q ha hb
    | true =>
      simp only [d12972, d124458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d122305 q = 1) : d124459 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d124459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d122305 q = 1) : d159053 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d159053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d159053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d122305 q = 1) : d159054 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d159054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d159054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d122305 q = 1) : d159055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d159055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d159055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13110 q = 1) (hb : d122305 q = 1) : d159079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13110, d159079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13110, d159079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30958 (p : Pattern) (ha : d13116 p = 1) (hb : d122305 p = 1) : d159082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d122305 q = 1) : d159000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30926 q ha hb
    | true =>
      simp only [d12968, d159000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d122305 q = 1) : d159001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d159001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d122305 q = 1) : d159059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d159059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d159059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d122305 q = 1) : d159060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d159060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d159060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d122305 q = 1) : d159061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d159061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d159061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13116 q = 1) (hb : d122305 q = 1) : d159082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13116, d159082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13116, d159082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30959 (p : Pattern) (ha : d115405 p = 1) (hb : d122305 p = 1) : d159088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d122305 q = 1) : d159026 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d159026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30942 q ha hb
    | true =>
      simp only [d13005, d159026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30943 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d122305 q = 1) : d159027 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d159027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d159027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d122305 q = 1) : d159028 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d159028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d159028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d122305 q = 1) : d159029 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d159029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d159029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d122305 q = 1) : d159033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d159033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30944 q ha hb
    | true =>
      simp only [d13015, d159033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30945 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d122305 q = 1) : d159034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d159034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d159034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d122305 q = 1) : d159035 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d159035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d159035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d122305 q = 1) : d159057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d159057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30949 q ha hb
    | true =>
      simp only [d13051, d159057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30935 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d122305 q = 1) : d159058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d159058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d159058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d122305 q = 1) : d159063 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d159063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30950 q ha hb
    | true =>
      simp only [d13092, d159063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d122305 q = 1) : d159064 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d159064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d159064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d122305 q = 1) : d159065 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d159065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d159065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d122305 q = 1) : d159066 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d159066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d159066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d122305 q = 1) : d159067 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d159067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d159067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13100 q = 1) (hb : d122305 q = 1) : d159070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13100, d159070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30952 q ha hb
    | true =>
      simp only [d13100, d159070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30953 q ha hb
  have h16 (q : Pattern) (ha : d13101 q = 1) (hb : d122305 q = 1) : d159071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13101, d159071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13101, d159071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13102 q = 1) (hb : d122305 q = 1) : d159072 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13102, d159072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13102, d159072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13103 q = 1) (hb : d122305 q = 1) : d159073 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13103, d159073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13103, d159073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13106 q = 1) (hb : d122305 q = 1) : d159075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13106, d159075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30954 q ha hb
    | true =>
      simp only [d13106, d159075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30955 q ha hb
  have h20 (q : Pattern) (ha : d13107 q = 1) (hb : d122305 q = 1) : d159076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13107, d159076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13107, d159076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13108 q = 1) (hb : d122305 q = 1) : d159077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13108, d159077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13108, d159077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13111 q = 1) (hb : d122305 q = 1) : d159080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d159080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30956 q ha hb
    | true =>
      simp only [d13111, d159080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30957 q ha hb
  have h23 (q : Pattern) (ha : d115401 q = 1) (hb : d122305 q = 1) : d159081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d159081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115401, d159081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13117 q = 1) (hb : d122305 q = 1) : d159083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d159083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30958 q ha hb
    | true =>
      simp only [d13117, d159083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13118 q = 1) (hb : d122305 q = 1) : d159084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d159084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13118, d159084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115402 q = 1) (hb : d122305 q = 1) : d159085 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d159085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115402, d159085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115403 q = 1) (hb : d122305 q = 1) : d159086 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d159086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115403, d159086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115404 q = 1) (hb : d122305 q = 1) : d159087 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d159087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115404, d159087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115405 q = 1) (hb : d122305 q = 1) : d159088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d159088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115405, d159088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro30960 (p : Pattern) (ha : d115412 p = 1) (hb : d122305 p = 1) : d159102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13111 q = 1) (hb : d122305 q = 1) : d159080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d159080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30956 q ha hb
    | true =>
      simp only [d13111, d159080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30957 q ha hb
  have h2 (q : Pattern) (ha : d115401 q = 1) (hb : d122305 q = 1) : d159081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d159081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115401, d159081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13117 q = 1) (hb : d122305 q = 1) : d159083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d159083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30958 q ha hb
    | true =>
      simp only [d13117, d159083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13118 q = 1) (hb : d122305 q = 1) : d159084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d159084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13118, d159084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115402 q = 1) (hb : d122305 q = 1) : d159085 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d159085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115402, d159085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115410 q = 1) (hb : d122305 q = 1) : d159100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d159100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115410, d159100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115411 q = 1) (hb : d122305 q = 1) : d159101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d159101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115411, d159101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115412 q = 1) (hb : d122305 q = 1) : d159102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d159102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115412, d159102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30961 (p : Pattern) (ha : d13155 p = 1) (hb : d122305 p = 1) : d124595 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1379 q = 1) : d1379 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1383 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1384 q = 1) (hb : d122304 q = 1) : d14986 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, d122304, d14986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1384, d122304, d14986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13155 q = 1) (hb : d122305 q = 1) : d124595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13155, d122305, d124595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13155, d122305, d124595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30962 (p : Pattern) (ha : d13156 p = 1) (hb : d122305 p = 1) : d124596 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1383 q = 1) : d1383 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1389 q = 1) (hb : d122304 q = 1) : d14993 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d122304, d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1389, d122304, d14993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13156 q = 1) (hb : d122305 q = 1) : d124596 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13156, d122305, d124596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13156, d122305, d124596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30963 (p : Pattern) (ha : d13169 p = 1) (hb : d122305 p = 1) : d159108 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13163 q = 1) : d13163 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13167 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13168 q = 1) (hb : d122304 q = 1) : d15003 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13168, d122304, d15003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13168, d122304, d15003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13169 q = 1) (hb : d122305 q = 1) : d159108 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13169, d122305, d159108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13169, d122305, d159108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30964 (p : Pattern) (ha : d13179 p = 1) (hb : d122305 p = 1) : d159115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13157 q = 1) (hb : d122305 q = 1) : d124597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13157, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30961 q ha hb
    | true =>
      simp only [d13157, d124597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30962 q ha hb
  have h2 (q : Pattern) (ha : d13158 q = 1) (hb : d122305 q = 1) : d124598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13158, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13158, d124598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13159 q = 1) (hb : d122305 q = 1) : d124599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13159, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13159, d124599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13170 q = 1) (hb : d122305 q = 1) : d159109 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13170, d159109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30962 q ha hb
    | true =>
      simp only [d13170, d159109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30963 q ha hb
  have h5 (q : Pattern) (ha : d13171 q = 1) (hb : d122305 q = 1) : d159110 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13171, d159110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13171, d159110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13172 q = 1) (hb : d122305 q = 1) : d159111 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13172, d159111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13172, d159111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13173 q = 1) (hb : d122305 q = 1) : d159112 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13173, d159112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13173, d159112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13174 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30962 q ha hb
    | true =>
      simp only [d13174, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22005 q ha hb
  have h9 (q : Pattern) (ha : d13175 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13176 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6355 q = 1) (hb : d122305 q = 1) : d6355 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d6356 q = 1) (hb : d122305 q = 1) : d124610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22005 q ha hb
    | true =>
      simp only [d6356, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6357 q = 1) (hb : d122305 q = 1) : d124611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d6358 q = 1) (hb : d122305 q = 1) : d124612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13177 q = 1) (hb : d122305 q = 1) : d159113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13177, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13178 q = 1) (hb : d122305 q = 1) : d159114 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13178, d159114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13178, d159114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13179 q = 1) (hb : d122305 q = 1) : d159115 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13179, d159115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13179, d159115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro30965 (p : Pattern) (ha : d13183 p = 1) (hb : d122305 p = 1) : d159119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30962 q ha hb
    | true =>
      simp only [d13174, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22005 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6355 q = 1) (hb : d122305 q = 1) : d6355 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6356 q = 1) (hb : d122305 q = 1) : d124610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22005 q ha hb
    | true =>
      simp only [d6356, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6357 q = 1) (hb : d122305 q = 1) : d124611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6358 q = 1) (hb : d122305 q = 1) : d124612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13177 q = 1) (hb : d122305 q = 1) : d159113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6359 q = 1) (hb : d122305 q = 1) : d124613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6359, d124613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13182 q = 1) (hb : d122305 q = 1) : d159118 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13182, d159118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13182, d159118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13183 q = 1) (hb : d122305 q = 1) : d159119 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13183, d159119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13183, d159119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro30966 (p : Pattern) (ha : d13189 p = 1) (hb : d122305 p = 1) : d159125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13180 q = 1) (hb : d122305 q = 1) : d159116 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13180, d159116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30964 q ha hb
    | true =>
      simp only [d13180, d159116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13181 q = 1) (hb : d122305 q = 1) : d159117 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13181, d159117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13181, d159117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13184 q = 1) (hb : d122305 q = 1) : d159120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d159120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30965 q ha hb
    | true =>
      simp only [d13184, d159120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13185 q = 1) (hb : d122305 q = 1) : d159121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d159121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d159121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13186 q = 1) (hb : d122305 q = 1) : d159122 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13186, d159122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13186, d159122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13187 q = 1) (hb : d122305 q = 1) : d159123 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13187, d159123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13187, d159123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13188 q = 1) (hb : d122305 q = 1) : d159124 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13188, d159124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13188, d159124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13189 q = 1) (hb : d122305 q = 1) : d159125 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13189, d159125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13189, d159125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30967 (p : Pattern) (ha : d13202 p = 1) (hb : d122305 p = 1) : d159129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13184 q = 1) (hb : d122305 q = 1) : d159120 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d159120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30965 q ha hb
    | true =>
      simp only [d13184, d159120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13185 q = 1) (hb : d122305 q = 1) : d159121 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d159121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d159121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d122305 q = 1) : d124628 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30939 q ha hb
    | true =>
      simp only [d13197, d124628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d122305 q = 1) : d124629 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d124629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13199 q = 1) (hb : d122305 q = 1) : d159126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13199, d159126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13199, d159126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13200 q = 1) (hb : d122305 q = 1) : d159127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13200, d159127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13200, d159127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13201 q = 1) (hb : d122305 q = 1) : d159128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13201, d159128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13201, d159128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13202 q = 1) (hb : d122305 q = 1) : d159129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13202, d159129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13202, d159129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30968 (p : Pattern) (ha : d13243 p = 1) (hb : d122305 p = 1) : d159133 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d122305 q = 1) : d124602 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30962 q ha hb
    | true =>
      simp only [d13174, d124602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22005 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d122305 q = 1) : d124603 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d124603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d122305 q = 1) : d124604 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d124604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6355 q = 1) (hb : d122305 q = 1) : d6355 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6356 q = 1) (hb : d122305 q = 1) : d124610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22005 q ha hb
    | true =>
      simp only [d6356, d124610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6357 q = 1) (hb : d122305 q = 1) : d124611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d124611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6358 q = 1) (hb : d122305 q = 1) : d124612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d124612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13177 q = 1) (hb : d122305 q = 1) : d159113 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d159113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13190 q = 1) (hb : d122305 q = 1) : d13190 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13191 q = 1) (hb : d122305 q = 1) : d124622 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22005 q ha hb
    | true =>
      simp only [d13191, d124622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13192 q = 1) (hb : d122305 q = 1) : d124623 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d124623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13193 q = 1) (hb : d122305 q = 1) : d124624 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d124624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13194 q = 1) (hb : d122305 q = 1) : d124625 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13194, d124625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d13242 q = 1) (hb : d122305 q = 1) : d159132 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13242, d159132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13242, d159132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13243 q = 1) (hb : d122305 q = 1) : d159133 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13243, d159133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13243, d159133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro30969 (p : Pattern) (ha : d13249 p = 1) (hb : d122305 p = 1) : d159139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d122305 q = 1) : d159134 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d159134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30968 q ha hb
    | true =>
      simp only [d13244, d159134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d122305 q = 1) : d159135 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d159135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d159135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13246 q = 1) (hb : d122305 q = 1) : d159136 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13246, d159136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13246, d159136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13247 q = 1) (hb : d122305 q = 1) : d159137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13247, d159137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13247, d159137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13248 q = 1) (hb : d122305 q = 1) : d159138 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13248, d159138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13248, d159138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13249 q = 1) (hb : d122305 q = 1) : d159139 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13249, d159139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13249, d159139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30970 (p : Pattern) (ha : d115422 p = 1) (hb : d122305 p = 1) : d159145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13203 q = 1) (hb : d122305 q = 1) : d159130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13203, d159130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30966 q ha hb
    | true =>
      simp only [d13203, d159130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30967 q ha hb
  have h2 (q : Pattern) (ha : d115418 q = 1) (hb : d122305 q = 1) : d159131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d159131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115418, d159131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13250 q = 1) (hb : d122305 q = 1) : d159140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13250, d159140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30969 q ha hb
    | true =>
      simp only [d13250, d159140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13251 q = 1) (hb : d122305 q = 1) : d159141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13251, d159141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13251, d159141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115419 q = 1) (hb : d122305 q = 1) : d159142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d159142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115419, d159142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115420 q = 1) (hb : d122305 q = 1) : d159143 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d159143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115420, d159143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115421 q = 1) (hb : d122305 q = 1) : d159144 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d159144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115421, d159144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115422 q = 1) (hb : d122305 q = 1) : d159145 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d159145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115422, d159145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30971 (p : Pattern) (ha : d115428 p = 1) (hb : d122305 p = 1) : d159151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12988 q = 1) (hb : d122305 q = 1) : d159012 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12988, d159012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12988, d159012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30930 q ha hb
  have h2 (q : Pattern) (ha : d12989 q = 1) (hb : d122305 q = 1) : d159013 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12989, d159013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12989, d159013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12998 q = 1) (hb : d122305 q = 1) : d159021 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d159021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30930 q ha hb
    | true =>
      simp only [d12998, d159021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30933 q ha hb
  have h4 (q : Pattern) (ha : d12999 q = 1) (hb : d122305 q = 1) : d159022 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d159022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12999, d159022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13000 q = 1) (hb : d122305 q = 1) : d159023 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13000, d159023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13000, d159023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115406 q = 1) (hb : d122305 q = 1) : d159089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d159089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30951 q ha hb
    | true =>
      simp only [d115406, d159089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30959 q ha hb
  have h7 (q : Pattern) (ha : d13141 q = 1) (hb : d122305 q = 1) : d159096 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13141, d159096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30936 q ha hb
    | true =>
      simp only [d13141, d159096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30937 q ha hb
  have h8 (q : Pattern) (ha : d115407 q = 1) (hb : d122305 q = 1) : d159097 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d159097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115407, d159097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115408 q = 1) (hb : d122305 q = 1) : d159098 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d159098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115408, d159098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115409 q = 1) (hb : d122305 q = 1) : d159099 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d159099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115409, d159099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115413 q = 1) (hb : d122305 q = 1) : d159103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d159103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115413, d159103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30960 q ha hb
  have h12 (q : Pattern) (ha : d13150 q = 1) (hb : d122305 q = 1) : d124590 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13150, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13150, d124590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30938 q ha hb
  have h13 (q : Pattern) (ha : d115414 q = 1) (hb : d122305 q = 1) : d159104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d159104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115414, d159104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115415 q = 1) (hb : d122305 q = 1) : d159105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d159105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115415, d159105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115416 q = 1) (hb : d122305 q = 1) : d159106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d159106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115416, d159106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115417 q = 1) (hb : d122305 q = 1) : d159107 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d159107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115417, d159107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115423 q = 1) (hb : d122305 q = 1) : d159146 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d159146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115423, d159146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30970 q ha hb
  have h18 (q : Pattern) (ha : d13267 q = 1) (hb : d122305 q = 1) : d124661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13267, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13267, d124661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30941 q ha hb
  have h19 (q : Pattern) (ha : d115424 q = 1) (hb : d122305 q = 1) : d159147 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d159147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115424, d159147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115425 q = 1) (hb : d122305 q = 1) : d159148 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d159148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115425, d159148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115426 q = 1) (hb : d122305 q = 1) : d159149 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d159149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115426, d159149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115427 q = 1) (hb : d122305 q = 1) : d159150 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d159150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115427, d159150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115428 q = 1) (hb : d122305 q = 1) : d159151 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d159151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115428, d159151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30972 (p : Pattern) (ha : d115434 p = 1) (hb : d122305 p = 1) : d159157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115429 q = 1) (hb : d122305 q = 1) : d159152 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d159152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115429, d159152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30971 q ha hb
  have h2 (q : Pattern) (ha : d115430 q = 1) (hb : d122305 q = 1) : d159153 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d159153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115430, d159153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115431 q = 1) (hb : d122305 q = 1) : d159154 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d159154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115431, d159154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115432 q = 1) (hb : d122305 q = 1) : d159155 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d159155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115432, d159155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115433 q = 1) (hb : d122305 q = 1) : d159156 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d159156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115433, d159156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115434 q = 1) (hb : d122305 q = 1) : d159157 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d159157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115434, d159157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30973 (p : Pattern) (ha : d13282 p = 1) (hb : d122305 p = 1) : d124676 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1558 q = 1) : d1558 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1573 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1574 q = 1) (hb : d122304 q = 1) : d15150 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d122304, d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1574, d122304, d15150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13282 q = 1) (hb : d122305 q = 1) : d124676 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13282, d122305, d124676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13282, d122305, d124676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30974 (p : Pattern) (ha : d13293 p = 1) (hb : d122305 p = 1) : d159163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30973 q ha hb
    | true =>
      simp only [d13283, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22034 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5139 q = 1) (hb : d122305 q = 1) : d5139 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5140 q = 1) (hb : d122305 q = 1) : d124747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22034 q ha hb
    | true =>
      simp only [d5140, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5141 q = 1) (hb : d122305 q = 1) : d124748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5142 q = 1) (hb : d122305 q = 1) : d124749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13286 q = 1) (hb : d122305 q = 1) : d159161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13287 q = 1) (hb : d122305 q = 1) : d13287 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13288 q = 1) (hb : d122305 q = 1) : d124682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22034 q ha hb
    | true =>
      simp only [d13288, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13289 q = 1) (hb : d122305 q = 1) : d124683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13290 q = 1) (hb : d122305 q = 1) : d124684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13291 q = 1) (hb : d122305 q = 1) : d124685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13291, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d13292 q = 1) (hb : d122305 q = 1) : d159162 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13292, d159162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13292, d159162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13293 q = 1) (hb : d122305 q = 1) : d159163 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13293, d159163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d13293, d159163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
theorem andIntro30975 (p : Pattern) (ha : d13297 p = 1) (hb : d122305 p = 1) : d124691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13287 q = 1) (hb : d122305 q = 1) : d13287 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13288 q = 1) (hb : d122305 q = 1) : d124682 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22034 q ha hb
    | true =>
      simp only [d13288, d124682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13289 q = 1) (hb : d122305 q = 1) : d124683 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d124683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13290 q = 1) (hb : d122305 q = 1) : d124684 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d124684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13291 q = 1) (hb : d122305 q = 1) : d124685 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13291, d124685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13296 q = 1) (hb : d122305 q = 1) : d124690 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13296, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13296, d124690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13297 q = 1) (hb : d122305 q = 1) : d124691 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13297, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13297, d124691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30976 (p : Pattern) (ha : d13303 p = 1) (hb : d122305 p = 1) : d159169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30974 q ha hb
    | true =>
      simp only [d13294, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30975 q ha hb
    | true =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d122305 q = 1) : d159166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d122305 q = 1) : d159167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d122305 q = 1) : d159168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d159168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d159168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13303 q = 1) (hb : d122305 q = 1) : d159169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13303, d159169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13303, d159169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30977 (p : Pattern) (ha : d13307 p = 1) (hb : d122305 p = 1) : d124701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30975 q ha hb
    | true =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d122305 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d122305 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d122305 q = 1) : d124700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13307 q = 1) (hb : d122305 q = 1) : d124701 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13307, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13307, d124701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30978 (p : Pattern) (ha : d13313 p = 1) (hb : d122305 p = 1) : d159175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d122305 q = 1) : d159170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30976 q ha hb
    | true =>
      simp only [d13308, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30977 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d122305 q = 1) : d159171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d122305 q = 1) : d159172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d122305 q = 1) : d159173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d122305 q = 1) : d159174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13313 q = 1) (hb : d122305 q = 1) : d159175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13313, d159175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13313, d159175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30979 (p : Pattern) (ha : d13316 p = 1) (hb : d122305 p = 1) : d159178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30974 q ha hb
    | true =>
      simp only [d13294, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30975 q ha hb
    | true =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d122305 q = 1) : d159166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d122305 q = 1) : d159167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d122305 q = 1) : d159168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d159168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d159168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13316 q = 1) (hb : d122305 q = 1) : d159178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13316, d159178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13316, d159178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30980 (p : Pattern) (ha : d13317 p = 1) (hb : d122305 p = 1) : d124711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30975 q ha hb
    | true =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d122305 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d122305 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d122305 q = 1) : d124700 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d124700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13317 q = 1) (hb : d122305 q = 1) : d124711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13317, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13317, d124711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30981 (p : Pattern) (ha : d13323 p = 1) (hb : d122305 p = 1) : d159184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d122305 q = 1) : d159170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30976 q ha hb
    | true =>
      simp only [d13308, d159170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30977 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d122305 q = 1) : d159171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d159171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d122305 q = 1) : d159172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d159172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d122305 q = 1) : d159173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d159173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d122305 q = 1) : d159174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d159174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13318 q = 1) (hb : d122305 q = 1) : d159179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d159179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30979 q ha hb
    | true =>
      simp only [d13318, d159179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30980 q ha hb
  have h7 (q : Pattern) (ha : d13319 q = 1) (hb : d122305 q = 1) : d159180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d159180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13320 q = 1) (hb : d122305 q = 1) : d159181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13320, d159181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13321 q = 1) (hb : d122305 q = 1) : d159182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d159182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13322 q = 1) (hb : d122305 q = 1) : d159183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d159183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13323 q = 1) (hb : d122305 q = 1) : d159184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13323, d159184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13323, d159184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30982 (p : Pattern) (ha : d13366 p = 1) (hb : d122305 p = 1) : d159210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30973 q ha hb
    | true =>
      simp only [d13283, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22034 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5139 q = 1) (hb : d122305 q = 1) : d5139 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5140 q = 1) (hb : d122305 q = 1) : d124747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22034 q ha hb
    | true =>
      simp only [d5140, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5141 q = 1) (hb : d122305 q = 1) : d124748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5142 q = 1) (hb : d122305 q = 1) : d124749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13286 q = 1) (hb : d122305 q = 1) : d159161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d5143 q = 1) (hb : d122305 q = 1) : d124750 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5143, d124750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13365 q = 1) (hb : d122305 q = 1) : d159209 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13365, d159209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13365, d159209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13366 q = 1) (hb : d122305 q = 1) : d159210 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13366, d159210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13366, d159210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro30983 (p : Pattern) (ha : d13376 p = 1) (hb : d122305 p = 1) : d159220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d122305 q = 1) : d159211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30982 q ha hb
    | true =>
      simp only [d13367, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d122305 q = 1) : d159212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30975 q ha hb
    | true =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d122305 q = 1) : d159217 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d159217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d159217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d122305 q = 1) : d159218 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d159218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d159218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d122305 q = 1) : d159219 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d159219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d159219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13376 q = 1) (hb : d122305 q = 1) : d159220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13376, d159220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13376, d159220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30984 (p : Pattern) (ha : d13460 p = 1) (hb : d122305 p = 1) : d159259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13450 q = 1) (hb : d122305 q = 1) : d159254 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13450, d159254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30983 q ha hb
    | true =>
      simp only [d13450, d159254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30977 q ha hb
  have h2 (q : Pattern) (ha : d13451 q = 1) (hb : d122305 q = 1) : d159255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13451, d159255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13451, d159255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13452 q = 1) (hb : d122305 q = 1) : d159256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13452, d159256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13452, d159256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13453 q = 1) (hb : d122305 q = 1) : d159257 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13453, d159257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13453, d159257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13454 q = 1) (hb : d122305 q = 1) : d159258 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13454, d159258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13454, d159258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13455 q = 1) (hb : d122305 q = 1) : d124803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30977 q ha hb
    | true =>
      simp only [d13455, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13456 q = 1) (hb : d122305 q = 1) : d124804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13457 q = 1) (hb : d122305 q = 1) : d124805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13457, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13458 q = 1) (hb : d122305 q = 1) : d124806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13459 q = 1) (hb : d122305 q = 1) : d124807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13460 q = 1) (hb : d122305 q = 1) : d159259 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13460, d159259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13460, d159259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30985 (p : Pattern) (ha : d13466 p = 1) (hb : d122305 p = 1) : d124814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13455 q = 1) (hb : d122305 q = 1) : d124803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30977 q ha hb
    | true =>
      simp only [d13455, d124803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13456 q = 1) (hb : d122305 q = 1) : d124804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d124804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13457 q = 1) (hb : d122305 q = 1) : d124805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13457, d124805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13458 q = 1) (hb : d122305 q = 1) : d124806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d124806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13459 q = 1) (hb : d122305 q = 1) : d124807 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d124807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13461 q = 1) (hb : d122305 q = 1) : d124809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30980 q ha hb
    | true =>
      simp only [d13461, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13462 q = 1) (hb : d122305 q = 1) : d124810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13463 q = 1) (hb : d122305 q = 1) : d124811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13463, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13464 q = 1) (hb : d122305 q = 1) : d124812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13465 q = 1) (hb : d122305 q = 1) : d124813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13466 q = 1) (hb : d122305 q = 1) : d124814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13466, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13466, d124814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30986 (p : Pattern) (ha : d13475 p = 1) (hb : d122305 p = 1) : d124823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13461 q = 1) (hb : d122305 q = 1) : d124809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30980 q ha hb
    | true =>
      simp only [d13461, d124809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13462 q = 1) (hb : d122305 q = 1) : d124810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d124810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13463 q = 1) (hb : d122305 q = 1) : d124811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13463, d124811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13464 q = 1) (hb : d122305 q = 1) : d124812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d124812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13465 q = 1) (hb : d122305 q = 1) : d124813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d124813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13475 q = 1) (hb : d122305 q = 1) : d124823 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13475, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13475, d124823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30987 (p : Pattern) (ha : d13522 p = 1) (hb : d122305 p = 1) : d124861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13516 q = 1) (hb : d122305 q = 1) : d13516 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13517 q = 1) (hb : d122305 q = 1) : d124856 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22057 q ha hb
    | true =>
      simp only [d13517, d124856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13518 q = 1) (hb : d122305 q = 1) : d124857 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d124857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13519 q = 1) (hb : d122305 q = 1) : d124858 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d124858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13520 q = 1) (hb : d122305 q = 1) : d124859 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13520, d124859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13521 q = 1) (hb : d122305 q = 1) : d124860 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13521, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13521, d124860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13522 q = 1) (hb : d122305 q = 1) : d124861 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13522, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13522, d124861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro30988 (p : Pattern) (ha : d13586 p = 1) (hb : d122305 p = 1) : d124888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13523 q = 1) (hb : d122305 q = 1) : d124862 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30987 q ha hb
    | true =>
      simp only [d13523, d124862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13524 q = 1) (hb : d122305 q = 1) : d124863 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d124863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13583 q = 1) (hb : d122305 q = 1) : d124885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13583, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13583, d124885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13584 q = 1) (hb : d122305 q = 1) : d124886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13584, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13584, d124886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13585 q = 1) (hb : d122305 q = 1) : d124887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13585, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13585, d124887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13586 q = 1) (hb : d122305 q = 1) : d124888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13586, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13586, d124888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30989 (p : Pattern) (ha : d13592 p = 1) (hb : d122305 p = 1) : d124894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13587 q = 1) (hb : d122305 q = 1) : d124889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13587, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30988 q ha hb
    | true =>
      simp only [d13587, d124889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13588 q = 1) (hb : d122305 q = 1) : d124890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13588, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13588, d124890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13589 q = 1) (hb : d122305 q = 1) : d124891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13589, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13589, d124891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13590 q = 1) (hb : d122305 q = 1) : d124892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13590, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13590, d124892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13591 q = 1) (hb : d122305 q = 1) : d124893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13591, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13591, d124893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13592 q = 1) (hb : d122305 q = 1) : d124894 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13592, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13592, d124894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30990 (p : Pattern) (ha : d13328 p = 1) (hb : d122305 p = 1) : d159189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30974 q ha hb
    | true =>
      simp only [d13294, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30975 q ha hb
    | true =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d122305 q = 1) : d159166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d122305 q = 1) : d159167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d159167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d122305 q = 1) : d159188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d159188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d159188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13328 q = 1) (hb : d122305 q = 1) : d159189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13328, d159189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13328, d159189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30991 (p : Pattern) (ha : d13330 p = 1) (hb : d122305 p = 1) : d124724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30975 q ha hb
    | true =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d122305 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d122305 q = 1) : d124699 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d124699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d122305 q = 1) : d124723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d124723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13330 q = 1) (hb : d122305 q = 1) : d124724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13330, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13330, d124724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30992 (p : Pattern) (ha : d13337 p = 1) (hb : d122305 p = 1) : d159196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30974 q ha hb
    | true =>
      simp only [d13294, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30975 q ha hb
    | true =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d122305 q = 1) : d159166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d159166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d122305 q = 1) : d159194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d159194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d159194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d122305 q = 1) : d159195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d159195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d159195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13337 q = 1) (hb : d122305 q = 1) : d159196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13337, d159196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13337, d159196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30993 (p : Pattern) (ha : d13340 p = 1) (hb : d122305 p = 1) : d124734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d122305 q = 1) : d124692 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30975 q ha hb
    | true =>
      simp only [d13298, d124692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d122305 q = 1) : d124693 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d124693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d122305 q = 1) : d124698 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d124698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d122305 q = 1) : d124732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d124732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d122305 q = 1) : d124733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d124733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d122305 q = 1) : d124734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13340, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13340, d124734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30994 (p : Pattern) (ha : d13344 p = 1) (hb : d122305 p = 1) : d124738 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d1668 q = 1) : d1668 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1558 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1669 q = 1) (hb : d122304 q = 1) : d15228 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1669, d122304, d15228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1669, d122304, d15228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13344 q = 1) (hb : d122305 q = 1) : d124738 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13344, d122305, d124738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13344, d122305, d124738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30995 (p : Pattern) (ha : d13356 p = 1) (hb : d122305 p = 1) : d159200 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d13349 q = 1) : d13349 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13354 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13355 q = 1) (hb : d122304 q = 1) : d15236 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13355, d122304, d15236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13355, d122304, d15236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13356 q = 1) (hb : d122305 q = 1) : d159200 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13356, d122305, d159200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13356, d122305, d159200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro30996 (p : Pattern) (ha : d13362 p = 1) (hb : d122305 p = 1) : d159206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13345 q = 1) (hb : d122305 q = 1) : d124739 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13345, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30994 q ha hb
    | true =>
      simp only [d13345, d124739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30973 q ha hb
  have h2 (q : Pattern) (ha : d13346 q = 1) (hb : d122305 q = 1) : d124740 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13346, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13346, d124740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13347 q = 1) (hb : d122305 q = 1) : d124741 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13347, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13347, d124741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13357 q = 1) (hb : d122305 q = 1) : d159201 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13357, d159201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30973 q ha hb
    | true =>
      simp only [d13357, d159201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30995 q ha hb
  have h5 (q : Pattern) (ha : d13358 q = 1) (hb : d122305 q = 1) : d159202 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13358, d159202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13358, d159202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13359 q = 1) (hb : d122305 q = 1) : d159203 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13359, d159203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13359, d159203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13360 q = 1) (hb : d122305 q = 1) : d159204 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13360, d159204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13360, d159204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13283 q = 1) (hb : d122305 q = 1) : d124678 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30973 q ha hb
    | true =>
      simp only [d13283, d124678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22034 q ha hb
  have h9 (q : Pattern) (ha : d13284 q = 1) (hb : d122305 q = 1) : d124679 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d124679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13285 q = 1) (hb : d122305 q = 1) : d124680 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d124680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5139 q = 1) (hb : d122305 q = 1) : d5139 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5140 q = 1) (hb : d122305 q = 1) : d124747 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22034 q ha hb
    | true =>
      simp only [d5140, d124747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5141 q = 1) (hb : d122305 q = 1) : d124748 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d124748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5142 q = 1) (hb : d122305 q = 1) : d124749 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d124749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13286 q = 1) (hb : d122305 q = 1) : d159161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13286, d159161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13361 q = 1) (hb : d122305 q = 1) : d159205 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13361, d159205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13361, d159205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13362 q = 1) (hb : d122305 q = 1) : d159206 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13362, d159206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13362, d159206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro30997 (p : Pattern) (ha : d13372 p = 1) (hb : d122305 p = 1) : d159216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d122305 q = 1) : d159207 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d159207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30996 q ha hb
    | true =>
      simp only [d13363, d159207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d122305 q = 1) : d159208 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d159208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d159208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d122305 q = 1) : d159211 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30982 q ha hb
    | true =>
      simp only [d13367, d159211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d122305 q = 1) : d159212 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d159212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d122305 q = 1) : d159213 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d159213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d159213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d122305 q = 1) : d159214 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d159214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d159214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d122305 q = 1) : d159215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d159215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d159215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13372 q = 1) (hb : d122305 q = 1) : d159216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13372, d159216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13372, d159216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30998 (p : Pattern) (ha : d13417 p = 1) (hb : d122305 p = 1) : d159226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d122305 q = 1) : d159164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30974 q ha hb
    | true =>
      simp only [d13294, d159164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d122305 q = 1) : d159165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d159165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d122305 q = 1) : d159223 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d159223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d159223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d122305 q = 1) : d159224 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d159224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d159224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d122305 q = 1) : d159225 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d159225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d159225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13417 q = 1) (hb : d122305 q = 1) : d159226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13417, d159226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13417, d159226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30999 (p : Pattern) (ha : d115442 p = 1) (hb : d122305 p = 1) : d159232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d122305 q = 1) : d159190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d159190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30990 q ha hb
    | true =>
      simp only [d13331, d159190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30991 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d122305 q = 1) : d159191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d159191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d159191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d122305 q = 1) : d159192 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d159192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d159192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d122305 q = 1) : d159193 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d159193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d159193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d122305 q = 1) : d159197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d159197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30992 q ha hb
    | true =>
      simp only [d13341, d159197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30993 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d122305 q = 1) : d159198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d159198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d159198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d122305 q = 1) : d159199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d159199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d159199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d122305 q = 1) : d159221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d159221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30997 q ha hb
    | true =>
      simp only [d13377, d159221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30983 q ha hb
  have h9 (q : Pattern) (ha : d115438 q = 1) (hb : d122305 q = 1) : d159222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d159222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115438, d159222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d122305 q = 1) : d159227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d159227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30998 q ha hb
    | true =>
      simp only [d13418, d159227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d122305 q = 1) : d159228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d159228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d159228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115439 q = 1) (hb : d122305 q = 1) : d159229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d159229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d159229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115440 q = 1) (hb : d122305 q = 1) : d159230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d159230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115440, d159230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115441 q = 1) (hb : d122305 q = 1) : d159231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d159231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115441, d159231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115442 q = 1) (hb : d122305 q = 1) : d159232 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d159232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115442, d159232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
