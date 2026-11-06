import NetHack.Soko22Hazard87.AndIntroBlocks0432
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro108250 (p : Pattern) (ha : d47581 p = 1) (hb : d380473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47576 q = 1) (hb : d380468 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47576, d380468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108249 q ha hb
    | true =>
      simp only [d47576, d380468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47577 q = 1) (hb : d380469 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47577, d380469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47577, d380469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47578 q = 1) (hb : d380470 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47578, d380470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47578, d380470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47579 q = 1) (hb : d380471 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47579, d380471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47579, d380471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47580 q = 1) (hb : d380472 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47580, d380472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47580, d380472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47581 q = 1) (hb : d380473 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47581, d380473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47581, d380473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108251 (p : Pattern) (ha : d47587 p = 1) (hb : d380479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47582 q = 1) (hb : d380474 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47582, d380474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108250 q ha hb
    | true =>
      simp only [d47582, d380474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47583 q = 1) (hb : d380475 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47583, d380475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47583, d380475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47584 q = 1) (hb : d380476 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47584, d380476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47584, d380476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47585 q = 1) (hb : d380477 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47585, d380477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47585, d380477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47586 q = 1) (hb : d380478 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47586, d380478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47586, d380478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47587 q = 1) (hb : d380479 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47587, d380479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47587, d380479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108252 (p : Pattern) (ha : d47593 p = 1) (hb : d380485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47588 q = 1) (hb : d380480 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47588, d380480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108251 q ha hb
    | true =>
      simp only [d47588, d380480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47589 q = 1) (hb : d380481 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47589, d380481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47589, d380481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47590 q = 1) (hb : d380482 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47590, d380482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47590, d380482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47591 q = 1) (hb : d380483 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47591, d380483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47591, d380483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47592 q = 1) (hb : d380484 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47592, d380484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47592, d380484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47593 q = 1) (hb : d380485 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47593, d380485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47593, d380485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108253 (p : Pattern) (ha : d47599 p = 1) (hb : d380491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47594 q = 1) (hb : d380486 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47594, d380486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108252 q ha hb
    | true =>
      simp only [d47594, d380486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47595 q = 1) (hb : d380487 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47595, d380487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47595, d380487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47596 q = 1) (hb : d380488 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47596, d380488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47596, d380488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47597 q = 1) (hb : d380489 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47597, d380489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47597, d380489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47598 q = 1) (hb : d380490 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47598, d380490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47598, d380490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47599 q = 1) (hb : d380491 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47599, d380491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47599, d380491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108254 (p : Pattern) (ha : d47605 p = 1) (hb : d380497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47600 q = 1) (hb : d380492 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47600, d380492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108253 q ha hb
    | true =>
      simp only [d47600, d380492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47601 q = 1) (hb : d380493 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47601, d380493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47601, d380493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47602 q = 1) (hb : d380494 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47602, d380494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47602, d380494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47603 q = 1) (hb : d380495 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47603, d380495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47603, d380495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47604 q = 1) (hb : d380496 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47604, d380496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47604, d380496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47605 q = 1) (hb : d380497 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47605, d380497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47605, d380497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108255 (p : Pattern) (ha : d47611 p = 1) (hb : d380503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47606 q = 1) (hb : d380498 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47606, d380498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108254 q ha hb
    | true =>
      simp only [d47606, d380498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47607 q = 1) (hb : d380499 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47607, d380499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47607, d380499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47608 q = 1) (hb : d380500 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47608, d380500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47608, d380500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47609 q = 1) (hb : d380501 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47609, d380501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47609, d380501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47610 q = 1) (hb : d380502 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47610, d380502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47610, d380502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47611 q = 1) (hb : d380503 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47611, d380503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47611, d380503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108256 (p : Pattern) (ha : d0 p = 1) (hb : d380855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380855 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108257 (p : Pattern) (ha : d0 p = 1) (hb : d380503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380503 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108258 (p : Pattern) (ha : d0 p = 1) (hb : d380552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380552 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108259 (p : Pattern) (ha : d47575 p = 1) (hb : d381086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d47573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d381084 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d47574 q = 1) (hb : d381085 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47574, d381085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47574, d381085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d47575 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47575, d381086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47575, d381086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro108260 (p : Pattern) (ha : d47581 p = 1) (hb : d381086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47576 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108259 q ha hb
    | true =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47577 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47578 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47579 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47580 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47581 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108261 (p : Pattern) (ha : d47587 p = 1) (hb : d381086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47582 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108260 q ha hb
    | true =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47583 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47584 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47585 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47586 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47587 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108262 (p : Pattern) (ha : d47593 p = 1) (hb : d381086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47588 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108261 q ha hb
    | true =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47589 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47590 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47591 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47592 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47593 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108263 (p : Pattern) (ha : d47599 p = 1) (hb : d381086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47594 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108262 q ha hb
    | true =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47595 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47596 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47597 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47598 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47599 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108264 (p : Pattern) (ha : d47605 p = 1) (hb : d381086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47600 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108263 q ha hb
    | true =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47601 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47602 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47603 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47604 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47605 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108265 (p : Pattern) (ha : d47611 p = 1) (hb : d381086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47606 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108264 q ha hb
    | true =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47607 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47608 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47609 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47610 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47611 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108266 (p : Pattern) (ha : d0 p = 1) (hb : d381178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381178 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108267 (p : Pattern) (ha : d0 p = 1) (hb : d381086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381086 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108268 (p : Pattern) (ha : d0 p = 1) (hb : d381224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381224 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108269 (p : Pattern) (ha : d47575 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d47573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380708 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d47574 q = 1) (hb : d380709 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d47574, d380709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47574, d380709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d47575 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d47575, d380710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47575, d380710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro108270 (p : Pattern) (ha : d47581 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47576 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108269 q ha hb
    | true =>
      simp only [d47576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47577 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47578 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47579 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47580 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47581 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108271 (p : Pattern) (ha : d47587 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47582 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108270 q ha hb
    | true =>
      simp only [d47582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47583 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47584 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47585 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47586 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47587 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108272 (p : Pattern) (ha : d47593 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47588 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108271 q ha hb
    | true =>
      simp only [d47588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47589 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47590 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47591 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47592 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47593 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108273 (p : Pattern) (ha : d47599 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47594 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108272 q ha hb
    | true =>
      simp only [d47594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47595 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47596 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47597 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47598 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47599 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108274 (p : Pattern) (ha : d47605 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47600 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108273 q ha hb
    | true =>
      simp only [d47600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47601 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47602 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47603 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47604 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47605 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108275 (p : Pattern) (ha : d47611 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47606 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108274 q ha hb
    | true =>
      simp only [d47606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47607 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47608 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47609 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47610 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d47611 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro108276 (p : Pattern) (ha : d0 p = 1) (hb : d380710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380710 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108277 (p : Pattern) (ha : d0 p = 1) (hb : d381230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381230 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108278 (p : Pattern) (ha : d0 p = 1) (hb : d381239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381239 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108279 (p : Pattern) (ha : d0 p = 1) (hb : d381243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381243 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108280 (p : Pattern) (ha : d0 p = 1) (hb : d381250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381250 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108281 (p : Pattern) (ha : d0 p = 1) (hb : d381344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381344 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108282 (p : Pattern) (ha : d0 p = 1) (hb : d381297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381297 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108283 (p : Pattern) (ha : d0 p = 1) (hb : d380918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380918 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108284 (p : Pattern) (ha : d0 p = 1) (hb : d381350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381350 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108285 (p : Pattern) (ha : d0 p = 1) (hb : d381359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381359 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108286 (p : Pattern) (ha : d0 p = 1) (hb : d381363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381363 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108287 (p : Pattern) (ha : d0 p = 1) (hb : d381370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381370 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108288 (p : Pattern) (ha : d0 p = 1) (hb : d381376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381376 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108289 (p : Pattern) (ha : d0 p = 1) (hb : d381383 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381383 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro108290 (p : Pattern) (ha : d0 p = 1) (hb : d381391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d381391 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
end NetHack.Soko22Hazard87
