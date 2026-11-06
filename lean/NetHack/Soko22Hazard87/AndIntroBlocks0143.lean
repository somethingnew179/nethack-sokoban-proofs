import NetHack.Soko22Hazard87.AndIntroBlocks0142
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro35750 (p : Pattern) (ha : d142666 p = 1) (hb : d163577 p = 1) : d168660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163572 q = 1) : d168647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163572, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35749 q ha hb
    | true =>
      simp only [d163572, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163573 q = 1) : d168648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163573, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163573, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d142666 q = 1) : d168655 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35352 q ha hb
    | true =>
      simp only [d15442, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d142666 q = 1) : d168656 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163574 q = 1) : d168657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163574, d168657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163574, d168657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163575 q = 1) : d168658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163575, d168658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163575, d168658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163576 q = 1) : d168659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163576, d168659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163576, d168659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163577 q = 1) : d168660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163577, d168660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163577, d168660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35751 (p : Pattern) (ha : d142666 p = 1) (hb : d163583 p = 1) : d169041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163578 q = 1) : d169036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163578, d169036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35750 q ha hb
    | true =>
      simp only [d163578, d169036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35353 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163579 q = 1) : d169037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163579, d169037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163579, d169037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163580 q = 1) : d169038 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163580, d169038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163580, d169038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163581 q = 1) : d169039 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163581, d169039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163581, d169039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163582 q = 1) : d169040 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163582, d169040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163582, d169040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163583 q = 1) : d169041 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163583, d169041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163583, d169041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35752 (p : Pattern) (ha : d142666 p = 1) (hb : d163589 p = 1) : d169047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15208 q = 1) (hb : d142666 q = 1) : d168533 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d168533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35342 q ha hb
    | true =>
      simp only [d15208, d168533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35345 q ha hb
  have h2 (q : Pattern) (ha : d15209 q = 1) (hb : d142666 q = 1) : d168534 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d168534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15209, d168534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163562 q = 1) : d169028 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163562, d169028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163562, d169028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163563 q = 1) : d169029 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163563, d169029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163563, d169029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163565 q = 1) : d169031 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163565, d169031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163565, d169031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35748 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163566 q = 1) : d169032 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163566, d169032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163566, d169032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163567 q = 1) : d169033 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163567, d169033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163567, d169033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163568 q = 1) : d169034 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163568, d169034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163568, d169034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d142666 q = 1) (hb : d163569 q = 1) : d169035 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163569, d169035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163569, d169035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d142666 q = 1) (hb : d163584 q = 1) : d169042 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163584, d169042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163584, d169042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35751 q ha hb
  have h11 (q : Pattern) (ha : d142666 q = 1) (hb : d163585 q = 1) : d169043 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163585, d169043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163585, d169043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d142666 q = 1) (hb : d163586 q = 1) : d169044 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163586, d169044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163586, d169044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d142666 q = 1) (hb : d163587 q = 1) : d169045 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163587, d169045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163587, d169045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d142666 q = 1) (hb : d163588 q = 1) : d169046 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163588, d169046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163588, d169046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d142666 q = 1) (hb : d163589 q = 1) : d169047 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163589, d169047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163589, d169047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35753 (p : Pattern) (ha : d142666 p = 1) (hb : d163595 p = 1) : d169053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163590 q = 1) : d169048 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163590, d169048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163590, d169048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35752 q ha hb
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163591 q = 1) : d169049 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163591, d169049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163591, d169049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163592 q = 1) : d169050 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163592, d169050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163592, d169050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163593 q = 1) : d169051 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163593, d169051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163593, d169051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163594 q = 1) : d169052 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163594, d169052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163594, d169052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163595 q = 1) : d169053 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163595, d169053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163595, d169053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35754 (p : Pattern) (ha : d142666 p = 1) (hb : d163602 p = 1) : d169060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15594 q = 1) (hb : d142666 q = 1) : d168736 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d168736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35392 q ha hb
    | true =>
      simp only [d15594, d168736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35393 q ha hb
  have h2 (q : Pattern) (ha : d15595 q = 1) (hb : d142666 q = 1) : d168737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d168737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, d168737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15596 q = 1) (hb : d142666 q = 1) : d168738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d168738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15596, d168738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15597 q = 1) (hb : d142666 q = 1) : d168739 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d168739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d168739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15598 q = 1) (hb : d142666 q = 1) : d168740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d168740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d168740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163602 q = 1) : d169060 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163602, d169060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163602, d169060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro35755 (p : Pattern) (ha : d142666 p = 1) (hb : d163609 p = 1) : d168847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15786 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15787 q = 1) (hb : d142666 q = 1) : d168832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d142666, d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35424 q ha hb
    | true =>
      simp only [d15787, d142666, d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15788 q = 1) (hb : d142666 q = 1) : d168833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15789 q = 1) (hb : d142666 q = 1) : d168834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15795 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15796 q = 1) (hb : d142666 q = 1) : d168837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35400 q ha hb
    | true =>
      simp only [d15796, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15797 q = 1) (hb : d142666 q = 1) : d168838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15798 q = 1) (hb : d142666 q = 1) : d168839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15799 q = 1) (hb : d142666 q = 1) : d168840 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15799, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15814 q = 1) (hb : d142666 q = 1) : d168837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35400 q ha hb
    | true =>
      simp only [d15814, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15815 q = 1) (hb : d142666 q = 1) : d168838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15816 q = 1) (hb : d142666 q = 1) : d168839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15817 q = 1) (hb : d142666 q = 1) : d168845 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15817, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d142666 q = 1) (hb : d163608 q = 1) : d168846 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163608, d168846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d163608, d168846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d142666 q = 1) (hb : d163609 q = 1) : d168847 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163609, d168847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d163609, d168847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro35756 (p : Pattern) (ha : d142666 p = 1) (hb : d163615 p = 1) : d168861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163610 q = 1) : d168848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163610, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35755 q ha hb
    | true =>
      simp only [d163610, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163611 q = 1) : d168849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163611, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163611, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d142666 q = 1) : d168856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35401 q ha hb
    | true =>
      simp only [d15820, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d142666 q = 1) : d168857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163612 q = 1) : d168858 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163612, d168858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163612, d168858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163613 q = 1) : d168859 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163613, d168859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163613, d168859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163614 q = 1) : d168860 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163614, d168860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163614, d168860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163615 q = 1) : d168861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163615, d168861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163615, d168861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35757 (p : Pattern) (ha : d142666 p = 1) (hb : d163621 p = 1) : d169071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163616 q = 1) : d169066 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163616, d169066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35756 q ha hb
    | true =>
      simp only [d163616, d169066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35402 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163617 q = 1) : d169067 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163617, d169067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163617, d169067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163618 q = 1) : d169068 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163618, d169068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163618, d169068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163619 q = 1) : d169069 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163619, d169069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163619, d169069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163620 q = 1) : d169070 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163620, d169070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163620, d169070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163621 q = 1) : d169071 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163621, d169071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163621, d169071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35758 (p : Pattern) (ha : d142666 p = 1) (hb : d163627 p = 1) : d169077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15600 q = 1) (hb : d142666 q = 1) : d168742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, d168742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35391 q ha hb
    | true =>
      simp only [d15600, d168742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35394 q ha hb
  have h2 (q : Pattern) (ha : d15601 q = 1) (hb : d142666 q = 1) : d168743 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, d168743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15601, d168743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163600 q = 1) : d169058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163600, d169058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163600, d169058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163601 q = 1) : d169059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163601, d169059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163601, d169059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163603 q = 1) : d169061 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163603, d169061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163603, d169061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35754 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163604 q = 1) : d169062 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163604, d169062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163604, d169062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163605 q = 1) : d169063 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163605, d169063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163605, d169063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163606 q = 1) : d169064 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163606, d169064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163606, d169064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d142666 q = 1) (hb : d163607 q = 1) : d169065 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163607, d169065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163607, d169065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d142666 q = 1) (hb : d163622 q = 1) : d169072 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163622, d169072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163622, d169072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35757 q ha hb
  have h11 (q : Pattern) (ha : d142666 q = 1) (hb : d163623 q = 1) : d169073 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163623, d169073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163623, d169073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d142666 q = 1) (hb : d163624 q = 1) : d169074 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163624, d169074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163624, d169074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d142666 q = 1) (hb : d163625 q = 1) : d169075 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163625, d169075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163625, d169075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d142666 q = 1) (hb : d163626 q = 1) : d169076 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163626, d169076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163626, d169076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d142666 q = 1) (hb : d163627 q = 1) : d169077 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163627, d169077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163627, d169077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35759 (p : Pattern) (ha : d142666 p = 1) (hb : d163633 p = 1) : d169083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163628 q = 1) : d169078 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163628, d169078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163628, d169078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35758 q ha hb
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163629 q = 1) : d169079 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163629, d169079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163629, d169079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163630 q = 1) : d169080 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163630, d169080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163630, d169080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163631 q = 1) : d169081 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163631, d169081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163631, d169081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163632 q = 1) : d169082 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163632, d169082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163632, d169082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163633 q = 1) : d169083 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163633, d169083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163633, d169083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35760 (p : Pattern) (ha : d142666 p = 1) (hb : d163639 p = 1) : d169089 p = 1 := by
  have h0 (q : Pattern) (ha : d142666 q = 1) (hb : d163496 q = 1) : d168970 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163496, d168970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35733 q ha hb
    | true =>
      simp only [d163496, d168970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35737 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163523 q = 1) : d168997 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163523, d168997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163523, d168997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35741 q ha hb
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163524 q = 1) : d168998 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163524, d168998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163524, d168998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163559 q = 1) : d169025 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163559, d169025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163559, d169025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35747 q ha hb
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163560 q = 1) : d169026 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163560, d169026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163560, d169026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163561 q = 1) : d169027 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163561, d169027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163561, d169027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d142666 q = 1) (hb : d163596 q = 1) : d169054 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163596, d169054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163596, d169054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35753 q ha hb
  have h8 (q : Pattern) (ha : d142666 q = 1) (hb : d163597 q = 1) : d169055 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163597, d169055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163597, d169055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d142666 q = 1) (hb : d163598 q = 1) : d169056 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163598, d169056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163598, d169056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d142666 q = 1) (hb : d163599 q = 1) : d169057 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d163599, d169057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163599, d169057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d142666 q = 1) (hb : d163634 q = 1) : d169084 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163634, d169084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163634, d169084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35759 q ha hb
  have h12 (q : Pattern) (ha : d142666 q = 1) (hb : d163635 q = 1) : d169085 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163635, d169085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163635, d169085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d142666 q = 1) (hb : d163636 q = 1) : d169086 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163636, d169086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163636, d169086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d142666 q = 1) (hb : d163637 q = 1) : d169087 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d163637, d169087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163637, d169087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d142666 q = 1) (hb : d163638 q = 1) : d169088 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d163638, d169088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163638, d169088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d142666 q = 1) (hb : d163639 q = 1) : d169089 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d163639, d169089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d163639, d169089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro35761 (p : Pattern) (ha : d142666 p = 1) (hb : d163645 p = 1) : d169095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163640 q = 1) : d169090 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d163640, d169090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35760 q ha hb
    | true =>
      simp only [d163640, d169090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163641 q = 1) : d169091 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d163641, d169091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163641, d169091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163642 q = 1) : d169092 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d163642, d169092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163642, d169092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163643 q = 1) : d169093 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d163643, d169093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163643, d169093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163644 q = 1) : d169094 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d163644, d169094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163644, d169094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163645 q = 1) : d169095 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d163645, d169095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163645, d169095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35762 (p : Pattern) (ha : d142666 p = 1) (hb : d163651 p = 1) : d169101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163646 q = 1) : d169096 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d163646, d169096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35761 q ha hb
    | true =>
      simp only [d163646, d169096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163647 q = 1) : d169097 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d163647, d169097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163647, d169097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163648 q = 1) : d169098 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d163648, d169098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163648, d169098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163649 q = 1) : d169099 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d163649, d169099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163649, d169099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163650 q = 1) : d169100 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d163650, d169100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163650, d169100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163651 q = 1) : d169101 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d163651, d169101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163651, d169101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35763 (p : Pattern) (ha : d142666 p = 1) (hb : d163657 p = 1) : d169107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163652 q = 1) : d169102 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d163652, d169102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35762 q ha hb
    | true =>
      simp only [d163652, d169102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163653 q = 1) : d169103 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d163653, d169103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163653, d169103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163654 q = 1) : d169104 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d163654, d169104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163654, d169104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163655 q = 1) : d169105 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d163655, d169105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163655, d169105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163656 q = 1) : d169106 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d163656, d169106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163656, d169106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163657 q = 1) : d169107 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d163657, d169107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163657, d169107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35764 (p : Pattern) (ha : d142666 p = 1) (hb : d163663 p = 1) : d169113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163658 q = 1) : d169108 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d163658, d169108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35763 q ha hb
    | true =>
      simp only [d163658, d169108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163659 q = 1) : d169109 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d163659, d169109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163659, d169109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163660 q = 1) : d169110 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d163660, d169110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163660, d169110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163661 q = 1) : d169111 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d163661, d169111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163661, d169111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163662 q = 1) : d169112 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d163662, d169112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163662, d169112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163663 q = 1) : d169113 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d163663, d169113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163663, d169113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35765 (p : Pattern) (ha : d142666 p = 1) (hb : d163669 p = 1) : d169119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163664 q = 1) : d169114 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d163664, d169114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35764 q ha hb
    | true =>
      simp only [d163664, d169114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163665 q = 1) : d169115 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d163665, d169115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163665, d169115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163666 q = 1) : d169116 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d163666, d169116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163666, d169116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163667 q = 1) : d169117 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d163667, d169117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163667, d169117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163668 q = 1) : d169118 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d163668, d169118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163668, d169118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163669 q = 1) : d169119 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d163669, d169119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163669, d169119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35766 (p : Pattern) (ha : d142666 p = 1) (hb : d163675 p = 1) : d169125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163670 q = 1) : d169120 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d163670, d169120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35765 q ha hb
    | true =>
      simp only [d163670, d169120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163671 q = 1) : d169121 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d163671, d169121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163671, d169121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163672 q = 1) : d169122 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d163672, d169122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163672, d169122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163673 q = 1) : d169123 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d163673, d169123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163673, d169123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163674 q = 1) : d169124 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d163674, d169124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163674, d169124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163675 q = 1) : d169125 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d163675, d169125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163675, d169125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35767 (p : Pattern) (ha : d142666 p = 1) (hb : d163681 p = 1) : d169131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d142666 q = 1) (hb : d163676 q = 1) : d169126 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d163676, d169126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35766 q ha hb
    | true =>
      simp only [d163676, d169126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d142666 q = 1) (hb : d163677 q = 1) : d169127 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d163677, d169127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163677, d169127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d142666 q = 1) (hb : d163678 q = 1) : d169128 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d163678, d169128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163678, d169128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d142666 q = 1) (hb : d163679 q = 1) : d169129 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d163679, d169129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163679, d169129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d142666 q = 1) (hb : d163680 q = 1) : d169130 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d163680, d169130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163680, d169130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d142666 q = 1) (hb : d163681 q = 1) : d169131 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d163681, d169131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163681, d169131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35768 (p : Pattern) (ha : d120136 p = 1) (hb : d136963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136940 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136946 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d136958 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120079 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q ha hb
    | true =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120132 q = 1) (hb : d136959 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d136959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120132, d136959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d136870 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120133 q = 1) (hb : d136960 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d136960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120133, d136960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120134 q = 1) (hb : d136961 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d136961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120134, d136961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120135 q = 1) (hb : d136962 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d136962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120135, d136962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120136 q = 1) (hb : d136963 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120136, d136963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120136, d136963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35769 (p : Pattern) (ha : d120143 p = 1) (hb : d136979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136940 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136946 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136958 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120079 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q ha hb
    | true =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120132 q = 1) (hb : d136959 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d136959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120132, d136959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d136870 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120133 q = 1) (hb : d136960 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d136960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120133, d136960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120134 q = 1) (hb : d136961 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d136961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120134, d136961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120135 q = 1) (hb : d136962 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d136962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d136962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d136968 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d136972 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d136974 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d120086 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q ha hb
    | true =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d120139 q = 1) (hb : d136975 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d136975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d120139, d136975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d136877 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d120140 q = 1) (hb : d136976 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d136976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d120140, d136976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d120141 q = 1) (hb : d136977 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d136977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120141, d136977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120142 q = 1) (hb : d136978 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d136978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120142, d136978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d120143 q = 1) (hb : d136979 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120143, d136979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120143, d136979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35770 (p : Pattern) (ha : d120334 p = 1) (hb : d136988 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d136974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d120086 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q ha hb
    | true =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120139 q = 1) (hb : d136975 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d136975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120139, d136975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136877 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120140 q = 1) (hb : d136976 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d136976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120140, d136976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120141 q = 1) (hb : d136986 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d136986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120141, d136986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120142 q = 1) (hb : d136987 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d136987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120142, d136987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120334 q = 1) (hb : d136988 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120334, d136988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120334, d136988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35771 (p : Pattern) (ha : d120378 p = 1) (hb : d137010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137005 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d120115 q = 1) (hb : d136903 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120115, d136903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35451 q ha hb
    | true =>
      simp only [d120115, d136903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120374 q = 1) (hb : d137006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120374, d137006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120374, d137006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d136904 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120375 q = 1) (hb : d137007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120375, d137007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120375, d137007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120376 q = 1) (hb : d137008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120376, d137008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120376, d137008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120377 q = 1) (hb : d137009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120377, d137009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120377, d137009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120378 q = 1) (hb : d137010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120378, d137010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120378, d137010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35772 (p : Pattern) (ha : d121355 p = 1) (hb : d137016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136934 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120144 q = 1) (hb : d136980 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120144, d136980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35768 q ha hb
    | true =>
      simp only [d120144, d136980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35769 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136982 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120145 q = 1) (hb : d136983 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120145, d136983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120145, d136983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121345 q = 1) (hb : d136984 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121345, d136984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121345, d136984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121346 q = 1) (hb : d136985 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121346, d136985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121346, d136985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120335 q = 1) (hb : d136989 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120335, d136989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120335, d136989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35770 q ha hb
  have h8 (q : Pattern) (ha : d121347 q = 1) (hb : d136990 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121347, d136990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d121347, d136990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d121348 q = 1) (hb : d136991 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121348, d136991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d121348, d136991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d121349 q = 1) (hb : d136992 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121349, d136992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121349, d136992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d121350 q = 1) (hb : d136993 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121350, d136993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121350, d136993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d120379 q = 1) (hb : d137011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120379, d137011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120379, d137011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35771 q ha hb
  have h13 (q : Pattern) (ha : d121351 q = 1) (hb : d137012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121351, d137012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d121351, d137012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d121352 q = 1) (hb : d137013 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121352, d137013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121352, d137013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d121353 q = 1) (hb : d137014 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121353, d137014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d121353, d137014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d121354 q = 1) (hb : d137015 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121354, d137015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121354, d137015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d121355 q = 1) (hb : d137016 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d121355, d137016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d121355, d137016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro35773 (p : Pattern) (ha : d121361 p = 1) (hb : d137022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d136919 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d121356 q = 1) (hb : d137017 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d121356, d137017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121356, d137017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35772 q ha hb
  have h3 (q : Pattern) (ha : d121357 q = 1) (hb : d137018 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d121357, d137018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121357, d137018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121358 q = 1) (hb : d137019 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d121358, d137019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121358, d137019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121359 q = 1) (hb : d137020 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d121359, d137020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121359, d137020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121360 q = 1) (hb : d137021 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d121360, d137021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121360, d137021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121361 q = 1) (hb : d137022 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d121361, d137022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121361, d137022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro35774 (p : Pattern) (ha : d167255 p = 1) (hb : d168019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137043 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137049 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d167250 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d136958 q = 1) (hb : d167959 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35462 q ha hb
    | true =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q hb ha
  have h5 (q : Pattern) (ha : d167251 q = 1) (hb : d168015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167251, d168015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d167251, d168015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d137068 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d167252 q = 1) (hb : d168016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167252, d168016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167252, d168016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d167253 q = 1) (hb : d168017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167253, d168017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d167253, d168017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167254 q = 1) (hb : d168018 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167254, d168018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167254, d168018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167255 q = 1) (hb : d168019 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167255, d168019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167255, d168019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35775 (p : Pattern) (ha : d167262 p = 1) (hb : d168026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137043 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137049 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167250 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d136958 q = 1) (hb : d167959 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35462 q ha hb
    | true =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q hb ha
  have h4 (q : Pattern) (ha : d167251 q = 1) (hb : d168015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167251, d168015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d167251, d168015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d137068 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d167252 q = 1) (hb : d168016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167252, d168016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167252, d168016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167253 q = 1) (hb : d168017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167253, d168017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167253, d168017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167254 q = 1) (hb : d168018 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167254, d168018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167254, d168018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137077 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d137081 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d167257 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d136974 q = 1) (hb : d167966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136974, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35466 q ha hb
    | true =>
      simp only [d136974, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q hb ha
  have h13 (q : Pattern) (ha : d167258 q = 1) (hb : d168022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167258, d168022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d167258, d168022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137087 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d167259 q = 1) (hb : d168023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167259, d168023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167259, d168023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167260 q = 1) (hb : d168024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167260, d168024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d167260, d168024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167261 q = 1) (hb : d168025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167261, d168025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d167261, d168025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167262 q = 1) (hb : d168026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167262, d168026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167262, d168026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35776 (p : Pattern) (ha : d167269 p = 1) (hb : d168947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167257 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d136974 q = 1) (hb : d167966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136974, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35466 q ha hb
    | true =>
      simp only [d136974, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q hb ha
  have h3 (q : Pattern) (ha : d167258 q = 1) (hb : d168022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167258, d168022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167258, d168022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137087 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167259 q = 1) (hb : d168023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167259, d168023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167259, d168023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167267 q = 1) (hb : d168024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167267, d168024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167267, d168024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167268 q = 1) (hb : d168025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167268, d168025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167268, d168025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167269 q = 1) (hb : d168947 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167269, d168947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167269, d168947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35777 (p : Pattern) (ha : d167291 p = 1) (hb : d168957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167286 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137005 q = 1) (hb : d167997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137005, d167997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35471 q ha hb
    | true =>
      simp only [d137005, d167997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35451 q hb ha
  have h3 (q : Pattern) (ha : d167287 q = 1) (hb : d168953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167287, d168953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167287, d168953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d137126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167288 q = 1) (hb : d168954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167288, d168954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167288, d168954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167289 q = 1) (hb : d168955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167289, d168955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167289, d168955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167290 q = 1) (hb : d168956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167290, d168956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167290, d168956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167291 q = 1) (hb : d168957 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167291, d168957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167291, d168957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35778 (p : Pattern) (ha : d167297 p = 1) (hb : d168963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137037 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167263 q = 1) (hb : d168027 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167263, d168027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35774 q ha hb
    | true =>
      simp only [d167263, d168027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35775 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137094 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167264 q = 1) (hb : d168028 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167264, d168028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167264, d168028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167265 q = 1) (hb : d168945 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167265, d168945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167265, d168945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167266 q = 1) (hb : d168946 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167266, d168946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167266, d168946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167270 q = 1) (hb : d168948 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167270, d168948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d167270, d168948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35776 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d137103 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d167271 q = 1) (hb : d168949 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167271, d168949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167271, d168949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d167272 q = 1) (hb : d168950 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167272, d168950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167272, d168950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d167273 q = 1) (hb : d168951 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167273, d168951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167273, d168951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d167274 q = 1) (hb : d168952 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167274, d168952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167274, d168952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d167292 q = 1) (hb : d168958 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167292, d168958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d167292, d168958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35777 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d167293 q = 1) (hb : d168959 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167293, d168959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167293, d168959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167294 q = 1) (hb : d168960 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167294, d168960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167294, d168960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d167295 q = 1) (hb : d168961 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167295, d168961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167295, d168961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d167296 q = 1) (hb : d168962 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167296, d168962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167296, d168962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d167297 q = 1) (hb : d168963 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167297, d168963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d167297, d168963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35779 (p : Pattern) (ha : d167303 p = 1) (hb : d168969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167298 q = 1) (hb : d168964 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167298, d168964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167298, d168964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35778 q ha hb
  have h2 (q : Pattern) (ha : d167299 q = 1) (hb : d168965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167299, d168965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167299, d168965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167300 q = 1) (hb : d168966 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167300, d168966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167300, d168966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167301 q = 1) (hb : d168967 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167301, d168967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167301, d168967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167302 q = 1) (hb : d168968 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167302, d168968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167302, d168968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167303 q = 1) (hb : d168969 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167303, d168969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167303, d168969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35780 (p : Pattern) (ha : d167327 p = 1) (hb : d168152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137207 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d167316 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d137172 q = 1) (hb : d168147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137172, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35516 q ha hb
    | true =>
      simp only [d137172, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35506 q hb ha
  have h5 (q : Pattern) (ha : d167317 q = 1) (hb : d168148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167317, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d167317, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d167323 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d167324 q = 1) (hb : d168149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167324, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167324, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d167325 q = 1) (hb : d168150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167325, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d167325, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167326 q = 1) (hb : d168151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167326, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167326, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167327 q = 1) (hb : d168152 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167327, d168152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167327, d168152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35781 (p : Pattern) (ha : d167337 p = 1) (hb : d168161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137198 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d137207 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167316 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137172 q = 1) (hb : d168147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137172, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35516 q ha hb
    | true =>
      simp only [d137172, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35506 q hb ha
  have h4 (q : Pattern) (ha : d167317 q = 1) (hb : d168148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167317, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d167317, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d167323 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d167324 q = 1) (hb : d168149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167324, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167324, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167325 q = 1) (hb : d168150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167325, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167325, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167326 q = 1) (hb : d168151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167326, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167326, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d137243 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d137248 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d167329 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d137182 q = 1) (hb : d168156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137182, d168156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35518 q ha hb
    | true =>
      simp only [d137182, d168156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35507 q hb ha
  have h13 (q : Pattern) (ha : d167330 q = 1) (hb : d168157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167330, d168157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d167330, d168157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d167333 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d167334 q = 1) (hb : d168158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167334, d168158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167334, d168158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167335 q = 1) (hb : d168159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167335, d168159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d167335, d168159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167336 q = 1) (hb : d168160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167336, d168160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d167336, d168160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167337 q = 1) (hb : d168161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167337, d168161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167337, d168161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35782 (p : Pattern) (ha : d167344 p = 1) (hb : d168973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167329 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137182 q = 1) (hb : d168156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137182, d168156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35518 q ha hb
    | true =>
      simp only [d137182, d168156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35507 q hb ha
  have h3 (q : Pattern) (ha : d167330 q = 1) (hb : d168157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167330, d168157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167330, d168157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167333 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167334 q = 1) (hb : d168158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167334, d168158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167334, d168158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167342 q = 1) (hb : d168159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167342, d168159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167342, d168159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167343 q = 1) (hb : d168160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167343, d168160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167343, d168160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167344 q = 1) (hb : d168973 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167344, d168973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167344, d168973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35783 (p : Pattern) (ha : d167372 p = 1) (hb : d168984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167361 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d137320 q = 1) (hb : d168979 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137320, d168979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35543 q ha hb
    | true =>
      simp only [d137320, d168979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35512 q hb ha
  have h3 (q : Pattern) (ha : d167362 q = 1) (hb : d168980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167362, d168980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167362, d168980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167368 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167369 q = 1) (hb : d168981 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167369, d168981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167369, d168981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167370 q = 1) (hb : d168982 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167370, d168982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167370, d168982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167371 q = 1) (hb : d168983 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167371, d168983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167371, d168983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167372 q = 1) (hb : d168984 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167372, d168984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167372, d168984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35784 (p : Pattern) (ha : d167378 p = 1) (hb : d168990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d137190 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167338 q = 1) (hb : d168162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167338, d168162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35780 q ha hb
    | true =>
      simp only [d167338, d168162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35781 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d137272 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167339 q = 1) (hb : d168163 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167339, d168163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167339, d168163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167340 q = 1) (hb : d168971 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167340, d168971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167340, d168971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167341 q = 1) (hb : d168972 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167341, d168972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167341, d168972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167345 q = 1) (hb : d168974 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167345, d168974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d167345, d168974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35782 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d137281 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d167346 q = 1) (hb : d168975 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167346, d168975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167346, d168975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d167347 q = 1) (hb : d168976 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167347, d168976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167347, d168976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d167348 q = 1) (hb : d168977 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167348, d168977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167348, d168977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d167349 q = 1) (hb : d168978 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167349, d168978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167349, d168978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d167373 q = 1) (hb : d168985 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167373, d168985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d167373, d168985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35783 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137346 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d167374 q = 1) (hb : d168986 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167374, d168986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167374, d168986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167375 q = 1) (hb : d168987 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167375, d168987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167375, d168987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d167376 q = 1) (hb : d168988 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167376, d168988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167376, d168988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d167377 q = 1) (hb : d168989 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167377, d168989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167377, d168989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d167378 q = 1) (hb : d168990 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167378, d168990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d167378, d168990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35785 (p : Pattern) (ha : d167384 p = 1) (hb : d168996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167379 q = 1) (hb : d168991 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167379, d168991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167379, d168991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35784 q ha hb
  have h2 (q : Pattern) (ha : d167380 q = 1) (hb : d168992 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167380, d168992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167380, d168992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167381 q = 1) (hb : d168993 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167381, d168993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167381, d168993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167382 q = 1) (hb : d168994 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167382, d168994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167382, d168994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167383 q = 1) (hb : d168995 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167383, d168995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167383, d168995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167384 q = 1) (hb : d168996 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167384, d168996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167384, d168996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35786 (p : Pattern) (ha : d167459 p = 1) (hb : d168314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167427 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d167448 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d167398 q = 1) (hb : d168309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167398, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35569 q ha hb
    | true =>
      simp only [d167398, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35555 q ha hb
  have h5 (q : Pattern) (ha : d167449 q = 1) (hb : d168310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167449, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d167449, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d167455 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d167456 q = 1) (hb : d168311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167456, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167456, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d167457 q = 1) (hb : d168312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167457, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d167457, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167458 q = 1) (hb : d168313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167458, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167458, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167459 q = 1) (hb : d168314 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167459, d168314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167459, d168314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35787 (p : Pattern) (ha : d167479 p = 1) (hb : d168324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d167421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167427 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167448 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167398 q = 1) (hb : d168309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167398, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35569 q ha hb
    | true =>
      simp only [d167398, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35555 q ha hb
  have h4 (q : Pattern) (ha : d167449 q = 1) (hb : d168310 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167449, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d167449, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d167455 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d167456 q = 1) (hb : d168311 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167456, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167456, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167457 q = 1) (hb : d168312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167457, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167457, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167458 q = 1) (hb : d168313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167458, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167458, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d167464 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d167468 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d167471 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d167407 q = 1) (hb : d168319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167407, d168319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35571 q ha hb
    | true =>
      simp only [d167407, d168319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35556 q ha hb
  have h13 (q : Pattern) (ha : d167472 q = 1) (hb : d168320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167472, d168320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d167472, d168320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d167475 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d167476 q = 1) (hb : d168321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167476, d168321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167476, d168321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167477 q = 1) (hb : d168322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167477, d168322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d167477, d168322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167478 q = 1) (hb : d168323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167478, d168323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d167478, d168323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167479 q = 1) (hb : d168324 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167479, d168324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167479, d168324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35788 (p : Pattern) (ha : d167493 p = 1) (hb : d169001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167471 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d167407 q = 1) (hb : d168319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167407, d168319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35571 q ha hb
    | true =>
      simp only [d167407, d168319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35556 q ha hb
  have h3 (q : Pattern) (ha : d167472 q = 1) (hb : d168320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167472, d168320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167472, d168320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167475 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167476 q = 1) (hb : d168321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167476, d168321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167476, d168321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167491 q = 1) (hb : d168322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167491, d168322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167491, d168322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167492 q = 1) (hb : d168323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167492, d168323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167492, d168323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167493 q = 1) (hb : d169001 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167493, d169001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167493, d169001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35789 (p : Pattern) (ha : d167530 p = 1) (hb : d168452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167525 q = 1) (hb : d168439 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167525, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35605 q ha hb
    | true =>
      simp only [d167525, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167526 q = 1) (hb : d168440 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167526, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167526, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137519 q = 1) (hb : d168447 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137519, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35560 q ha hb
    | true =>
      simp only [d137519, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137520 q = 1) (hb : d168448 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137520, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137520, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167527 q = 1) (hb : d168449 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167527, d168449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167527, d168449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167528 q = 1) (hb : d168450 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167528, d168450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167528, d168450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167529 q = 1) (hb : d168451 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167529, d168451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167529, d168451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167530 q = 1) (hb : d168452 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167530, d168452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167530, d168452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35790 (p : Pattern) (ha : d167542 p = 1) (hb : d169012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167522 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d167531 q = 1) (hb : d169007 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167531, d169007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35789 q ha hb
    | true =>
      simp only [d167531, d169007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35561 q ha hb
  have h3 (q : Pattern) (ha : d167532 q = 1) (hb : d169008 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167532, d169008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167532, d169008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167538 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167539 q = 1) (hb : d169009 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167539, d169009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167539, d169009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167540 q = 1) (hb : d169010 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167540, d169010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167540, d169010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167541 q = 1) (hb : d169011 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167541, d169011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167541, d169011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167542 q = 1) (hb : d169012 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167542, d169012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167542, d169012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35791 (p : Pattern) (ha : d167548 p = 1) (hb : d169018 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d167415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167480 q = 1) (hb : d168325 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167480, d168325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35786 q ha hb
    | true =>
      simp only [d167480, d168325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35787 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167487 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167488 q = 1) (hb : d168326 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167488, d168326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167488, d168326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167489 q = 1) (hb : d168999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167489, d168999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167489, d168999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167490 q = 1) (hb : d169000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167490, d169000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167490, d169000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167494 q = 1) (hb : d169002 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167494, d169002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d167494, d169002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35788 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d137491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d167495 q = 1) (hb : d169003 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167495, d169003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167495, d169003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d167496 q = 1) (hb : d169004 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167496, d169004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167496, d169004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d167497 q = 1) (hb : d169005 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167497, d169005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167497, d169005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d167498 q = 1) (hb : d169006 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167498, d169006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167498, d169006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d167543 q = 1) (hb : d169013 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167543, d169013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d167543, d169013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35790 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137556 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d167544 q = 1) (hb : d169014 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167544, d169014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167544, d169014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167545 q = 1) (hb : d169015 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167545, d169015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167545, d169015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d167546 q = 1) (hb : d169016 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167546, d169016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167546, d169016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d167547 q = 1) (hb : d169017 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167547, d169017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167547, d169017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d167548 q = 1) (hb : d169018 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167548, d169018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d167548, d169018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35792 (p : Pattern) (ha : d167554 p = 1) (hb : d169024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167549 q = 1) (hb : d169019 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167549, d169019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167549, d169019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35791 q ha hb
  have h2 (q : Pattern) (ha : d167550 q = 1) (hb : d169020 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167550, d169020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167550, d169020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167551 q = 1) (hb : d169021 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167551, d169021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167551, d169021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167552 q = 1) (hb : d169022 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167552, d169022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167552, d169022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167553 q = 1) (hb : d169023 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167553, d169023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167553, d169023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167554 q = 1) (hb : d169024 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167554, d169024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167554, d169024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35793 (p : Pattern) (ha : d167630 p = 1) (hb : d168522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167592 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d167619 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d167569 q = 1) (hb : d168517 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167569, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35628 q ha hb
    | true =>
      simp only [d167569, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35614 q ha hb
  have h5 (q : Pattern) (ha : d167620 q = 1) (hb : d168518 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167620, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d167620, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d167626 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d167627 q = 1) (hb : d168519 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167627, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167627, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d167628 q = 1) (hb : d168520 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167628, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d167628, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167629 q = 1) (hb : d168521 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167629, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167629, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167630 q = 1) (hb : d168522 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167630, d168522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167630, d168522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35794 (p : Pattern) (ha : d167650 p = 1) (hb : d168532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d167592 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167619 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167569 q = 1) (hb : d168517 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167569, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35628 q ha hb
    | true =>
      simp only [d167569, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35614 q ha hb
  have h4 (q : Pattern) (ha : d167620 q = 1) (hb : d168518 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167620, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d167620, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d167626 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d167627 q = 1) (hb : d168519 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167627, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167627, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167628 q = 1) (hb : d168520 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167628, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167628, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167629 q = 1) (hb : d168521 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167629, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167629, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d167635 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d167639 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d167642 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d167578 q = 1) (hb : d168527 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167578, d168527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35630 q ha hb
    | true =>
      simp only [d167578, d168527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35615 q ha hb
  have h13 (q : Pattern) (ha : d167643 q = 1) (hb : d168528 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167643, d168528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d167643, d168528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d167646 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d167647 q = 1) (hb : d168529 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167647, d168529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167647, d168529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167648 q = 1) (hb : d168530 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167648, d168530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d167648, d168530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167649 q = 1) (hb : d168531 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167649, d168531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d167649, d168531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167650 q = 1) (hb : d168532 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167650, d168532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167650, d168532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35795 (p : Pattern) (ha : d167664 p = 1) (hb : d169030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167642 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d167578 q = 1) (hb : d168527 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167578, d168527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35630 q ha hb
    | true =>
      simp only [d167578, d168527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35615 q ha hb
  have h3 (q : Pattern) (ha : d167643 q = 1) (hb : d168528 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167643, d168528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167643, d168528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167646 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167647 q = 1) (hb : d168529 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167647, d168529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167647, d168529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167662 q = 1) (hb : d168530 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167662, d168530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167662, d168530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167663 q = 1) (hb : d168531 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167663, d168531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167663, d168531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167664 q = 1) (hb : d169030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167664, d169030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167664, d169030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35796 (p : Pattern) (ha : d167701 p = 1) (hb : d168660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167696 q = 1) (hb : d168647 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167696, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35664 q ha hb
    | true =>
      simp only [d167696, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167697 q = 1) (hb : d168648 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167697, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167697, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137730 q = 1) (hb : d168655 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137730, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35619 q ha hb
    | true =>
      simp only [d137730, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137731 q = 1) (hb : d168656 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137731, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137731, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167698 q = 1) (hb : d168657 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167698, d168657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167698, d168657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167699 q = 1) (hb : d168658 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167699, d168658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167699, d168658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167700 q = 1) (hb : d168659 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167700, d168659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167700, d168659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167701 q = 1) (hb : d168660 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167701, d168660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167701, d168660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35797 (p : Pattern) (ha : d167713 p = 1) (hb : d169041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167693 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d167702 q = 1) (hb : d169036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167702, d169036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35796 q ha hb
    | true =>
      simp only [d167702, d169036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35620 q ha hb
  have h3 (q : Pattern) (ha : d167703 q = 1) (hb : d169037 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167703, d169037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167703, d169037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167709 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167710 q = 1) (hb : d169038 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167710, d169038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167710, d169038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167711 q = 1) (hb : d169039 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167711, d169039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167711, d169039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167712 q = 1) (hb : d169040 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167712, d169040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167712, d169040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167713 q = 1) (hb : d169041 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167713, d169041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167713, d169041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35798 (p : Pattern) (ha : d167719 p = 1) (hb : d169047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d167586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167651 q = 1) (hb : d168533 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167651, d168533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35793 q ha hb
    | true =>
      simp only [d167651, d168533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35794 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167659 q = 1) (hb : d168534 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167659, d168534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167659, d168534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167660 q = 1) (hb : d169028 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167660, d169028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167660, d169028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167661 q = 1) (hb : d169029 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167661, d169029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167661, d169029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167665 q = 1) (hb : d169031 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167665, d169031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d167665, d169031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35795 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d137702 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d167666 q = 1) (hb : d169032 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167666, d169032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167666, d169032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d167667 q = 1) (hb : d169033 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167667, d169033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167667, d169033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d167668 q = 1) (hb : d169034 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167668, d169034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167668, d169034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d167669 q = 1) (hb : d169035 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167669, d169035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167669, d169035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d167714 q = 1) (hb : d169042 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167714, d169042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d167714, d169042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35797 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137767 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d167715 q = 1) (hb : d169043 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167715, d169043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167715, d169043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167716 q = 1) (hb : d169044 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167716, d169044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167716, d169044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d167717 q = 1) (hb : d169045 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167717, d169045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167717, d169045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d167718 q = 1) (hb : d169046 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167718, d169046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167718, d169046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d167719 q = 1) (hb : d169047 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167719, d169047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d167719, d169047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35799 (p : Pattern) (ha : d167725 p = 1) (hb : d169053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167720 q = 1) (hb : d169048 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167720, d169048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167720, d169048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35798 q ha hb
  have h2 (q : Pattern) (ha : d167721 q = 1) (hb : d169049 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167721, d169049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167721, d169049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167722 q = 1) (hb : d169050 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167722, d169050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167722, d169050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167723 q = 1) (hb : d169051 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167723, d169051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167723, d169051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167724 q = 1) (hb : d169052 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167724, d169052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167724, d169052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167725 q = 1) (hb : d169053 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167725, d169053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167725, d169053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35800 (p : Pattern) (ha : d167802 p = 1) (hb : d168731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d167791 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d167741 q = 1) (hb : d168726 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167741, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35685 q ha hb
    | true =>
      simp only [d167741, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35672 q ha hb
  have h5 (q : Pattern) (ha : d167792 q = 1) (hb : d168727 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167792, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d167792, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d167798 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d167799 q = 1) (hb : d168728 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167799, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167799, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d167800 q = 1) (hb : d168729 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167800, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d167800, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167801 q = 1) (hb : d168730 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167801, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167801, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167802 q = 1) (hb : d168731 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167802, d168731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167802, d168731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35801 (p : Pattern) (ha : d167822 p = 1) (hb : d168741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d167764 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167741 q = 1) (hb : d168726 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167741, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35685 q ha hb
    | true =>
      simp only [d167741, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35672 q ha hb
  have h4 (q : Pattern) (ha : d167792 q = 1) (hb : d168727 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167792, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d167792, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d167798 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d167799 q = 1) (hb : d168728 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167799, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167799, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167800 q = 1) (hb : d168729 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167800, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167800, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167801 q = 1) (hb : d168730 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167801, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167801, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d167807 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d167811 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d167814 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d167750 q = 1) (hb : d168736 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167750, d168736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35687 q ha hb
    | true =>
      simp only [d167750, d168736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35673 q ha hb
  have h13 (q : Pattern) (ha : d167815 q = 1) (hb : d168737 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167815, d168737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d167815, d168737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d167818 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d167819 q = 1) (hb : d168738 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167819, d168738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167819, d168738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167820 q = 1) (hb : d168739 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167820, d168739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d167820, d168739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d167821 q = 1) (hb : d168740 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167821, d168740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d167821, d168740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d167822 q = 1) (hb : d168741 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167822, d168741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167822, d168741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35802 (p : Pattern) (ha : d167836 p = 1) (hb : d169060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167814 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d167750 q = 1) (hb : d168736 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167750, d168736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35687 q ha hb
    | true =>
      simp only [d167750, d168736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35673 q ha hb
  have h3 (q : Pattern) (ha : d167815 q = 1) (hb : d168737 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167815, d168737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167815, d168737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167818 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167819 q = 1) (hb : d168738 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167819, d168738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167819, d168738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167834 q = 1) (hb : d168739 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167834, d168739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167834, d168739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167835 q = 1) (hb : d168740 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167835, d168740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167835, d168740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167836 q = 1) (hb : d169060 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167836, d169060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167836, d169060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35803 (p : Pattern) (ha : d167873 p = 1) (hb : d168861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167868 q = 1) (hb : d168848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167868, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35717 q ha hb
    | true =>
      simp only [d167868, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167869 q = 1) (hb : d168849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167869, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167869, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137942 q = 1) (hb : d168856 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d137942, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35677 q ha hb
    | true =>
      simp only [d137942, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137943 q = 1) (hb : d168857 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137943, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137943, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167870 q = 1) (hb : d168858 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167870, d168858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167870, d168858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167871 q = 1) (hb : d168859 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167871, d168859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167871, d168859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167872 q = 1) (hb : d168860 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167872, d168860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167872, d168860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167873 q = 1) (hb : d168861 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167873, d168861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167873, d168861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35804 (p : Pattern) (ha : d167885 p = 1) (hb : d169071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167865 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d167874 q = 1) (hb : d169066 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167874, d169066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35803 q ha hb
    | true =>
      simp only [d167874, d169066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35678 q ha hb
  have h3 (q : Pattern) (ha : d167875 q = 1) (hb : d169067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167875, d169067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167875, d169067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167881 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167882 q = 1) (hb : d169068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167882, d169068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167882, d169068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167883 q = 1) (hb : d169069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167883, d169069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167883, d169069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167884 q = 1) (hb : d169070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167884, d169070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167884, d169070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167885 q = 1) (hb : d169071 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167885, d169071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167885, d169071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35805 (p : Pattern) (ha : d167891 p = 1) (hb : d169077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d167758 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167823 q = 1) (hb : d168742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167823, d168742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35800 q ha hb
    | true =>
      simp only [d167823, d168742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35801 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167830 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167831 q = 1) (hb : d168743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167831, d168743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167831, d168743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d167832 q = 1) (hb : d169058 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167832, d169058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167832, d169058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d167833 q = 1) (hb : d169059 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167833, d169059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167833, d169059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167837 q = 1) (hb : d169061 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167837, d169061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d167837, d169061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35802 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d137914 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d167838 q = 1) (hb : d169062 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167838, d169062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167838, d169062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d167839 q = 1) (hb : d169063 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167839, d169063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167839, d169063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d167840 q = 1) (hb : d169064 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167840, d169064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167840, d169064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d167841 q = 1) (hb : d169065 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167841, d169065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167841, d169065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d167886 q = 1) (hb : d169072 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d167886, d169072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d167886, d169072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35804 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d137979 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d167887 q = 1) (hb : d169073 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d167887, d169073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d167887, d169073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d167888 q = 1) (hb : d169074 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d167888, d169074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167888, d169074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d167889 q = 1) (hb : d169075 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d167889, d169075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d167889, d169075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d167890 q = 1) (hb : d169076 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d167890, d169076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d167890, d169076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d167891 q = 1) (hb : d169077 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d167891, d169077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d167891, d169077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35806 (p : Pattern) (ha : d167897 p = 1) (hb : d169083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167892 q = 1) (hb : d169078 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d167892, d169078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167892, d169078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35805 q ha hb
  have h2 (q : Pattern) (ha : d167893 q = 1) (hb : d169079 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d167893, d169079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167893, d169079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d167894 q = 1) (hb : d169080 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d167894, d169080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167894, d169080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167895 q = 1) (hb : d169081 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d167895, d169081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167895, d169081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167896 q = 1) (hb : d169082 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d167896, d169082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167896, d169082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167897 q = 1) (hb : d169083 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d167897, d169083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167897, d169083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35807 (p : Pattern) (ha : d167903 p = 1) (hb : d169089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d167304 q = 1) (hb : d168970 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167304, d168970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35773 q hb ha
    | true =>
      simp only [d167304, d168970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35779 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d167385 q = 1) (hb : d168997 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167385, d168997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167385, d168997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35785 q ha hb
  have h3 (q : Pattern) (ha : d167386 q = 1) (hb : d168998 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d167386, d168998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d167386, d168998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d167555 q = 1) (hb : d169025 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167555, d169025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167555, d169025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35792 q ha hb
  have h5 (q : Pattern) (ha : d167556 q = 1) (hb : d169026 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d167556, d169026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167556, d169026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167557 q = 1) (hb : d169027 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d167557, d169027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167557, d169027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167726 q = 1) (hb : d169054 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167726, d169054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167726, d169054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35799 q ha hb
  have h8 (q : Pattern) (ha : d167727 q = 1) (hb : d169055 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d167727, d169055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167727, d169055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167728 q = 1) (hb : d169056 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d167728, d169056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167728, d169056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d167729 q = 1) (hb : d169057 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d167729, d169057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167729, d169057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d167898 q = 1) (hb : d169084 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d167898, d169084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167898, d169084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35806 q ha hb
  have h12 (q : Pattern) (ha : d167899 q = 1) (hb : d169085 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d167899, d169085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167899, d169085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d167900 q = 1) (hb : d169086 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d167900, d169086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167900, d169086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167901 q = 1) (hb : d169087 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d167901, d169087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d167901, d169087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167902 q = 1) (hb : d169088 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d167902, d169088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167902, d169088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167903 q = 1) (hb : d169089 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d167903, d169089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167903, d169089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro35808 (p : Pattern) (ha : d167909 p = 1) (hb : d169095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167904 q = 1) (hb : d169090 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d167904, d169090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35807 q ha hb
    | true =>
      simp only [d167904, d169090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167905 q = 1) (hb : d169091 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d167905, d169091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167905, d169091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167906 q = 1) (hb : d169092 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d167906, d169092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167906, d169092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167907 q = 1) (hb : d169093 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d167907, d169093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167907, d169093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167908 q = 1) (hb : d169094 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d167908, d169094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167908, d169094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167909 q = 1) (hb : d169095 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d167909, d169095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167909, d169095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35809 (p : Pattern) (ha : d167915 p = 1) (hb : d169101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167910 q = 1) (hb : d169096 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d167910, d169096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35808 q ha hb
    | true =>
      simp only [d167910, d169096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167911 q = 1) (hb : d169097 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d167911, d169097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167911, d169097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167912 q = 1) (hb : d169098 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d167912, d169098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167912, d169098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167913 q = 1) (hb : d169099 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d167913, d169099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167913, d169099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167914 q = 1) (hb : d169100 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d167914, d169100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167914, d169100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167915 q = 1) (hb : d169101 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d167915, d169101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167915, d169101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35810 (p : Pattern) (ha : d167921 p = 1) (hb : d169107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167916 q = 1) (hb : d169102 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d167916, d169102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35809 q ha hb
    | true =>
      simp only [d167916, d169102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167917 q = 1) (hb : d169103 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d167917, d169103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167917, d169103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167918 q = 1) (hb : d169104 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d167918, d169104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167918, d169104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167919 q = 1) (hb : d169105 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d167919, d169105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167919, d169105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167920 q = 1) (hb : d169106 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d167920, d169106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167920, d169106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167921 q = 1) (hb : d169107 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d167921, d169107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167921, d169107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35811 (p : Pattern) (ha : d167927 p = 1) (hb : d169113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167922 q = 1) (hb : d169108 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d167922, d169108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35810 q ha hb
    | true =>
      simp only [d167922, d169108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167923 q = 1) (hb : d169109 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d167923, d169109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167923, d169109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167924 q = 1) (hb : d169110 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d167924, d169110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167924, d169110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167925 q = 1) (hb : d169111 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d167925, d169111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167925, d169111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167926 q = 1) (hb : d169112 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d167926, d169112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167926, d169112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167927 q = 1) (hb : d169113 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d167927, d169113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167927, d169113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35812 (p : Pattern) (ha : d167933 p = 1) (hb : d169119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167928 q = 1) (hb : d169114 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d167928, d169114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35811 q ha hb
    | true =>
      simp only [d167928, d169114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167929 q = 1) (hb : d169115 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d167929, d169115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167929, d169115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167930 q = 1) (hb : d169116 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d167930, d169116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167930, d169116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167931 q = 1) (hb : d169117 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d167931, d169117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167931, d169117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167932 q = 1) (hb : d169118 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d167932, d169118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167932, d169118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167933 q = 1) (hb : d169119 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d167933, d169119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167933, d169119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35813 (p : Pattern) (ha : d167939 p = 1) (hb : d169125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167934 q = 1) (hb : d169120 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d167934, d169120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35812 q ha hb
    | true =>
      simp only [d167934, d169120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167935 q = 1) (hb : d169121 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d167935, d169121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167935, d169121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167936 q = 1) (hb : d169122 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d167936, d169122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167936, d169122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167937 q = 1) (hb : d169123 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d167937, d169123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167937, d169123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167938 q = 1) (hb : d169124 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d167938, d169124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167938, d169124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167939 q = 1) (hb : d169125 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d167939, d169125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167939, d169125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35814 (p : Pattern) (ha : d167945 p = 1) (hb : d169131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167940 q = 1) (hb : d169126 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d167940, d169126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35813 q ha hb
    | true =>
      simp only [d167940, d169126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167941 q = 1) (hb : d169127 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d167941, d169127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167941, d169127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d167942 q = 1) (hb : d169128 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d167942, d169128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167942, d169128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d167943 q = 1) (hb : d169129 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d167943, d169129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167943, d169129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d167944 q = 1) (hb : d169130 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d167944, d169130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167944, d169130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167945 q = 1) (hb : d169131 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d167945, d169131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167945, d169131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35815 (p : Pattern) (ha : d120136 p = 1) (hb : d139462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135515 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135521 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d135533 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120132 q = 1) (hb : d139458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d139458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120132, d139458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d135445 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d120133 q = 1) (hb : d139459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d139459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120133, d139459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120134 q = 1) (hb : d139460 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d139460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120134, d139460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d120135 q = 1) (hb : d139461 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d139461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120135, d139461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120136 q = 1) (hb : d139462 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120136, d139462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120136, d139462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35816 (p : Pattern) (ha : d120143 p = 1) (hb : d139467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135515 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135521 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135533 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d120079 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d120132 q = 1) (hb : d139458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d139458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120132, d139458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135445 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d120133 q = 1) (hb : d139459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d139459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120133, d139459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120134 q = 1) (hb : d139460 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d139460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120134, d139460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120135 q = 1) (hb : d139461 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d139461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d139461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d135555 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d135559 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d135561 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d120139 q = 1) (hb : d139463 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d139463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120139, d139463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d135452 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d120140 q = 1) (hb : d139464 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d139464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d120140, d139464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120141 q = 1) (hb : d139465 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d139465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120141, d139465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d120142 q = 1) (hb : d139466 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d139466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120142, d139466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120143 q = 1) (hb : d139467 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120143, d139467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120143, d139467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35817 (p : Pattern) (ha : d120334 p = 1) (hb : d139474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120086 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120139 q = 1) (hb : d139463 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d139463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120139, d139463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d135452 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120140 q = 1) (hb : d139464 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d139464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120140, d139464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120141 q = 1) (hb : d139472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d139472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120141, d139472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120142 q = 1) (hb : d139473 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d139473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120142, d139473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120334 q = 1) (hb : d139474 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120334, d139474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120334, d139474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35818 (p : Pattern) (ha : d120378 p = 1) (hb : d139484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d120115 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120374 q = 1) (hb : d139480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120374, d139480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120374, d139480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d135479 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d120375 q = 1) (hb : d139481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120375, d139481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120375, d139481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120376 q = 1) (hb : d139482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120376, d139482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120376, d139482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120377 q = 1) (hb : d139483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120377, d139483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120377, d139483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120378 q = 1) (hb : d139484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120378, d139484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120378, d139484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35819 (p : Pattern) (ha : d121355 p = 1) (hb : d139490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135509 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120144 q = 1) (hb : d139468 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120144, d139468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35815 q ha hb
    | true =>
      simp only [d120144, d139468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35816 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d120145 q = 1) (hb : d139469 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120145, d139469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120145, d139469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d121345 q = 1) (hb : d139470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121345, d139470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d121345, d139470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121346 q = 1) (hb : d139471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121346, d139471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121346, d139471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120335 q = 1) (hb : d139475 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120335, d139475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120335, d139475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35817 q ha hb
  have h8 (q : Pattern) (ha : d121347 q = 1) (hb : d139476 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121347, d139476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d121347, d139476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d121348 q = 1) (hb : d139477 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121348, d139477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d121348, d139477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d121349 q = 1) (hb : d139478 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121349, d139478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d121349, d139478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d121350 q = 1) (hb : d139479 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121350, d139479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d121350, d139479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d120379 q = 1) (hb : d139485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120379, d139485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120379, d139485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35818 q ha hb
  have h13 (q : Pattern) (ha : d121351 q = 1) (hb : d139486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d121351, d139486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d121351, d139486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d121352 q = 1) (hb : d139487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d121352, d139487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d121352, d139487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d121353 q = 1) (hb : d139488 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d121353, d139488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d121353, d139488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d121354 q = 1) (hb : d139489 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d121354, d139489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d121354, d139489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d121355 q = 1) (hb : d139490 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d121355, d139490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d121355, d139490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro35820 (p : Pattern) (ha : d121361 p = 1) (hb : d139496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135494 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d121356 q = 1) (hb : d139491 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d121356, d139491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121356, d139491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35819 q ha hb
  have h3 (q : Pattern) (ha : d121357 q = 1) (hb : d139492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d121357, d139492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121357, d139492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d121358 q = 1) (hb : d139493 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d121358, d139493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121358, d139493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d121359 q = 1) (hb : d139494 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d121359, d139494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121359, d139494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d121360 q = 1) (hb : d139495 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d121360, d139495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121360, d139495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d121361 q = 1) (hb : d139496 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d121361, d139496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121361, d139496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro35821 (p : Pattern) (ha : d168019 p = 1) (hb : d169136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135650 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d166480 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167959 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168015 q = 1) (hb : d169132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168015, d169132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168015, d169132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d135681 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d168016 q = 1) (hb : d169133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168016, d169133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d168016, d169133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168017 q = 1) (hb : d169134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168017, d169134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d168017, d169134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d168018 q = 1) (hb : d169135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168018, d169135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168018, d169135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d168019 q = 1) (hb : d169136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168019, d169136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168019, d169136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35822 (p : Pattern) (ha : d168026 p = 1) (hb : d169141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135644 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135650 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d166480 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d167959 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d168015 q = 1) (hb : d169132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168015, d169132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d168015, d169132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d135681 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d168016 q = 1) (hb : d169133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168016, d169133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d168016, d169133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168017 q = 1) (hb : d169134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168017, d169134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168017, d169134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168018 q = 1) (hb : d169135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168018, d169135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168018, d169135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d135690 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d135694 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d166487 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d167966 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d168022 q = 1) (hb : d169137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168022, d169137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d168022, d169137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d135702 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d168023 q = 1) (hb : d169138 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168023, d169138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d168023, d169138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d168024 q = 1) (hb : d169139 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168024, d169139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d168024, d169139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d168025 q = 1) (hb : d169140 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168025, d169140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d168025, d169140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d168026 q = 1) (hb : d169141 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168026, d169141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d168026, d169141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35823 (p : Pattern) (ha : d168947 p = 1) (hb : d169148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167966 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168022 q = 1) (hb : d169137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168022, d169137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168022, d169137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d135702 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168023 q = 1) (hb : d169138 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168023, d169138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168023, d169138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168024 q = 1) (hb : d169146 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168024, d169146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168024, d169146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168025 q = 1) (hb : d169147 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168025, d169147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168025, d169147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168947 q = 1) (hb : d169148 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168947, d169148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168947, d169148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35824 (p : Pattern) (ha : d168957 p = 1) (hb : d169158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166516 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167997 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168953 q = 1) (hb : d169154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168953, d169154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168953, d169154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d135753 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168954 q = 1) (hb : d169155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168954, d169155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168954, d169155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168955 q = 1) (hb : d169156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168955, d169156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168955, d169156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168956 q = 1) (hb : d169157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168956, d169157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168956, d169157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168957 q = 1) (hb : d169158 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168957, d169158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168957, d169158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35825 (p : Pattern) (ha : d168963 p = 1) (hb : d169164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135638 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d168027 q = 1) (hb : d169142 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d168027, d169142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35821 q ha hb
    | true =>
      simp only [d168027, d169142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35822 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168028 q = 1) (hb : d169143 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d168028, d169143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168028, d169143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168945 q = 1) (hb : d169144 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d168945, d169144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168945, d169144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168946 q = 1) (hb : d169145 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d168946, d169145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168946, d169145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168948 q = 1) (hb : d169149 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d168948, d169149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d168948, d169149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35823 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d135718 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d168949 q = 1) (hb : d169150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d168949, d169150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d168949, d169150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d168950 q = 1) (hb : d169151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d168950, d169151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d168950, d169151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d168951 q = 1) (hb : d169152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d168951, d169152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d168951, d169152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d168952 q = 1) (hb : d169153 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d168952, d169153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d168952, d169153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d168958 q = 1) (hb : d169159 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d168958, d169159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d168958, d169159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35824 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d135764 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d168959 q = 1) (hb : d169160 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d168959, d169160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d168959, d169160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d168960 q = 1) (hb : d169161 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d168960, d169161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d168960, d169161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d168961 q = 1) (hb : d169162 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d168961, d169162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d168961, d169162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d168962 q = 1) (hb : d169163 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d168962, d169163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d168962, d169163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d168963 q = 1) (hb : d169164 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d168963, d169164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d168963, d169164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35826 (p : Pattern) (ha : d168969 p = 1) (hb : d169170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d168964 q = 1) (hb : d169165 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d168964, d169165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168964, d169165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35825 q ha hb
  have h2 (q : Pattern) (ha : d168965 q = 1) (hb : d169166 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d168965, d169166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168965, d169166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d168966 q = 1) (hb : d169167 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d168966, d169167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168966, d169167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d168967 q = 1) (hb : d169168 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d168967, d169168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168967, d169168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d168968 q = 1) (hb : d169169 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d168968, d169169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168968, d169169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168969 q = 1) (hb : d169170 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d168969, d169170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168969, d169170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35827 (p : Pattern) (ha : d168152 p = 1) (hb : d169176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135834 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d166546 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d168147 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168148 q = 1) (hb : d169172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168148, d169172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168148, d169172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d166553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d168149 q = 1) (hb : d169173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168149, d169173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d168149, d169173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168150 q = 1) (hb : d169174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168150, d169174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d168150, d169174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d168151 q = 1) (hb : d169175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168151, d169175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168151, d169175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d168152 q = 1) (hb : d169176 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168152, d169176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168152, d169176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35828 (p : Pattern) (ha : d168161 p = 1) (hb : d169181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135825 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d135834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d166546 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d168147 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d168148 q = 1) (hb : d169172 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168148, d169172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d168148, d169172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d166553 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d168149 q = 1) (hb : d169173 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168149, d169173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d168149, d169173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168150 q = 1) (hb : d169174 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168150, d169174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168150, d169174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168151 q = 1) (hb : d169175 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168151, d169175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168151, d169175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d135893 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d135898 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d166559 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d168156 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d168157 q = 1) (hb : d169177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168157, d169177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d168157, d169177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d166563 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d168158 q = 1) (hb : d169178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168158, d169178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d168158, d169178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d168159 q = 1) (hb : d169179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168159, d169179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d168159, d169179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d168160 q = 1) (hb : d169180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168160, d169180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d168160, d169180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d168161 q = 1) (hb : d169181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168161, d169181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d168161, d169181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35829 (p : Pattern) (ha : d168973 p = 1) (hb : d169188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166559 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d168156 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168157 q = 1) (hb : d169177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168157, d169177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168157, d169177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d166563 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168158 q = 1) (hb : d169178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168158, d169178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168158, d169178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168159 q = 1) (hb : d169186 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168159, d169186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168159, d169186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168160 q = 1) (hb : d169187 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168160, d169187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168160, d169187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168973 q = 1) (hb : d169188 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168973, d169188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168973, d169188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35830 (p : Pattern) (ha : d168984 p = 1) (hb : d169198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166591 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d168979 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168980 q = 1) (hb : d169194 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168980, d169194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168980, d169194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d166598 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168981 q = 1) (hb : d169195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168981, d169195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168981, d169195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168982 q = 1) (hb : d169196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168982, d169196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168982, d169196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168983 q = 1) (hb : d169197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168983, d169197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168983, d169197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168984 q = 1) (hb : d169198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168984, d169198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168984, d169198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35831 (p : Pattern) (ha : d168990 p = 1) (hb : d169204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d135817 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d168162 q = 1) (hb : d169182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d168162, d169182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35827 q ha hb
    | true =>
      simp only [d168162, d169182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35828 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d135925 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168163 q = 1) (hb : d169183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d168163, d169183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168163, d169183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168971 q = 1) (hb : d169184 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d168971, d169184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168971, d169184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168972 q = 1) (hb : d169185 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d168972, d169185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168972, d169185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168974 q = 1) (hb : d169189 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d168974, d169189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d168974, d169189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35829 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d135934 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d168975 q = 1) (hb : d169190 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d168975, d169190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d168975, d169190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d168976 q = 1) (hb : d169191 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d168976, d169191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d168976, d169191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d168977 q = 1) (hb : d169192 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d168977, d169192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d168977, d169192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d168978 q = 1) (hb : d169193 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d168978, d169193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d168978, d169193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d168985 q = 1) (hb : d169199 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d168985, d169199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d168985, d169199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35830 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136021 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d168986 q = 1) (hb : d169200 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d168986, d169200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d168986, d169200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d168987 q = 1) (hb : d169201 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d168987, d169201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d168987, d169201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d168988 q = 1) (hb : d169202 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d168988, d169202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d168988, d169202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d168989 q = 1) (hb : d169203 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d168989, d169203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d168989, d169203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d168990 q = 1) (hb : d169204 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d168990, d169204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d168990, d169204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35832 (p : Pattern) (ha : d168996 p = 1) (hb : d169210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d168991 q = 1) (hb : d169205 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d168991, d169205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168991, d169205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35831 q ha hb
  have h2 (q : Pattern) (ha : d168992 q = 1) (hb : d169206 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d168992, d169206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168992, d169206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d168993 q = 1) (hb : d169207 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d168993, d169207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168993, d169207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d168994 q = 1) (hb : d169208 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d168994, d169208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168994, d169208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d168995 q = 1) (hb : d169209 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d168995, d169209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168995, d169209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168996 q = 1) (hb : d169210 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d168996, d169210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168996, d169210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35833 (p : Pattern) (ha : d168314 p = 1) (hb : d169217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d166657 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d166678 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d168309 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168310 q = 1) (hb : d169213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168310, d169213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168310, d169213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d166697 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d168311 q = 1) (hb : d169214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168311, d169214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d168311, d169214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168312 q = 1) (hb : d169215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168312, d169215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d168312, d169215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d168313 q = 1) (hb : d169216 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168313, d169216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168313, d169216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d168314 q = 1) (hb : d169217 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168314, d169217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168314, d169217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35834 (p : Pattern) (ha : d168324 p = 1) (hb : d169222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d166651 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166657 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d166678 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d168309 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d168310 q = 1) (hb : d169213 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168310, d169213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d168310, d169213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d166697 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d168311 q = 1) (hb : d169214 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168311, d169214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d168311, d169214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168312 q = 1) (hb : d169215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168312, d169215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168312, d169215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168313 q = 1) (hb : d169216 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168313, d169216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168313, d169216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d166706 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d166710 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d166713 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d168319 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d168320 q = 1) (hb : d169218 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168320, d169218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d168320, d169218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d166719 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d168321 q = 1) (hb : d169219 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168321, d169219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d168321, d169219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d168322 q = 1) (hb : d169220 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168322, d169220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d168322, d169220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d168323 q = 1) (hb : d169221 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168323, d169221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d168323, d169221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d168324 q = 1) (hb : d169222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168324, d169222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d168324, d169222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35835 (p : Pattern) (ha : d169001 p = 1) (hb : d169229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166713 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d168319 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168320 q = 1) (hb : d169218 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168320, d169218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168320, d169218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d166719 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168321 q = 1) (hb : d169219 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168321, d169219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168321, d169219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168322 q = 1) (hb : d169227 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168322, d169227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168322, d169227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168323 q = 1) (hb : d169228 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168323, d169228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168323, d169228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d169001 q = 1) (hb : d169229 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d169001, d169229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169001, d169229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35836 (p : Pattern) (ha : d169012 p = 1) (hb : d169239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d169007 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d169008 q = 1) (hb : d169235 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d169008, d169235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169008, d169235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d166789 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d169009 q = 1) (hb : d169236 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d169009, d169236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169009, d169236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169010 q = 1) (hb : d169237 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d169010, d169237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169010, d169237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169011 q = 1) (hb : d169238 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d169011, d169238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169011, d169238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d169012 q = 1) (hb : d169239 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d169012, d169239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169012, d169239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35837 (p : Pattern) (ha : d169018 p = 1) (hb : d169245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d166645 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d168325 q = 1) (hb : d169223 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d168325, d169223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35833 q ha hb
    | true =>
      simp only [d168325, d169223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35834 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d166731 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168326 q = 1) (hb : d169224 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d168326, d169224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168326, d169224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168999 q = 1) (hb : d169225 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d168999, d169225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168999, d169225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169000 q = 1) (hb : d169226 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d169000, d169226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169000, d169226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169002 q = 1) (hb : d169230 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d169002, d169230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169002, d169230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35835 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d136192 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d169003 q = 1) (hb : d169231 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d169003, d169231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d169003, d169231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169004 q = 1) (hb : d169232 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d169004, d169232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d169004, d169232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d169005 q = 1) (hb : d169233 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d169005, d169233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d169005, d169233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d169006 q = 1) (hb : d169234 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d169006, d169234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d169006, d169234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d169013 q = 1) (hb : d169240 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d169013, d169240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169013, d169240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35836 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136279 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d169014 q = 1) (hb : d169241 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d169014, d169241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d169014, d169241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d169015 q = 1) (hb : d169242 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d169015, d169242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d169015, d169242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d169016 q = 1) (hb : d169243 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d169016, d169243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d169016, d169243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d169017 q = 1) (hb : d169244 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d169017, d169244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d169017, d169244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d169018 q = 1) (hb : d169245 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d169018, d169245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d169018, d169245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35838 (p : Pattern) (ha : d169024 p = 1) (hb : d169251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169019 q = 1) (hb : d169246 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d169019, d169246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169019, d169246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35837 q ha hb
  have h2 (q : Pattern) (ha : d169020 q = 1) (hb : d169247 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d169020, d169247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169020, d169247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169021 q = 1) (hb : d169248 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d169021, d169248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169021, d169248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169022 q = 1) (hb : d169249 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d169022, d169249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169022, d169249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169023 q = 1) (hb : d169250 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d169023, d169250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169023, d169250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169024 q = 1) (hb : d169251 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d169024, d169251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169024, d169251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35839 (p : Pattern) (ha : d168522 p = 1) (hb : d169259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166843 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d166849 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d166870 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d168517 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168518 q = 1) (hb : d169255 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168518, d169255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168518, d169255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d166889 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d168519 q = 1) (hb : d169256 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168519, d169256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d168519, d169256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168520 q = 1) (hb : d169257 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168520, d169257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d168520, d169257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d168521 q = 1) (hb : d169258 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168521, d169258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168521, d169258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d168522 q = 1) (hb : d169259 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168522, d169259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168522, d169259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35840 (p : Pattern) (ha : d168532 p = 1) (hb : d169264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d166843 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166849 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d166870 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d168517 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d168518 q = 1) (hb : d169255 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168518, d169255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d168518, d169255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d166889 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d168519 q = 1) (hb : d169256 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168519, d169256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d168519, d169256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168520 q = 1) (hb : d169257 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168520, d169257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168520, d169257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168521 q = 1) (hb : d169258 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168521, d169258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168521, d169258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d166898 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d166902 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d166905 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d168527 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d168528 q = 1) (hb : d169260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168528, d169260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d168528, d169260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d166911 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d168529 q = 1) (hb : d169261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168529, d169261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d168529, d169261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d168530 q = 1) (hb : d169262 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168530, d169262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d168530, d169262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d168531 q = 1) (hb : d169263 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168531, d169263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d168531, d169263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d168532 q = 1) (hb : d169264 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168532, d169264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d168532, d169264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35841 (p : Pattern) (ha : d169030 p = 1) (hb : d169271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166905 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d168527 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168528 q = 1) (hb : d169260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168528, d169260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168528, d169260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d166911 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168529 q = 1) (hb : d169261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168529, d169261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168529, d169261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168530 q = 1) (hb : d169269 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168530, d169269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168530, d169269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168531 q = 1) (hb : d169270 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168531, d169270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168531, d169270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d169030 q = 1) (hb : d169271 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d169030, d169271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169030, d169271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35842 (p : Pattern) (ha : d169041 p = 1) (hb : d169281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d166958 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d169036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d169037 q = 1) (hb : d169277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d169037, d169277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169037, d169277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d166981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d169038 q = 1) (hb : d169278 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d169038, d169278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169038, d169278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169039 q = 1) (hb : d169279 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d169039, d169279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169039, d169279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169040 q = 1) (hb : d169280 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d169040, d169280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169040, d169280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d169041 q = 1) (hb : d169281 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d169041, d169281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169041, d169281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35843 (p : Pattern) (ha : d169047 p = 1) (hb : d169287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d166837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d168533 q = 1) (hb : d169265 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d168533, d169265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35839 q ha hb
    | true =>
      simp only [d168533, d169265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35840 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d166923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168534 q = 1) (hb : d169266 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d168534, d169266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168534, d169266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d169028 q = 1) (hb : d169267 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d169028, d169267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169028, d169267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169029 q = 1) (hb : d169268 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d169029, d169268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169029, d169268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169031 q = 1) (hb : d169272 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d169031, d169272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169031, d169272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35841 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d136451 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d169032 q = 1) (hb : d169273 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d169032, d169273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d169032, d169273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169033 q = 1) (hb : d169274 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d169033, d169274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d169033, d169274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d169034 q = 1) (hb : d169275 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d169034, d169275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d169034, d169275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d169035 q = 1) (hb : d169276 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d169035, d169276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d169035, d169276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d169042 q = 1) (hb : d169282 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d169042, d169282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169042, d169282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35842 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136538 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d169043 q = 1) (hb : d169283 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d169043, d169283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d169043, d169283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d169044 q = 1) (hb : d169284 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d169044, d169284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d169044, d169284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d169045 q = 1) (hb : d169285 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d169045, d169285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d169045, d169285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d169046 q = 1) (hb : d169286 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d169046, d169286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d169046, d169286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d169047 q = 1) (hb : d169287 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d169047, d169287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d169047, d169287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35844 (p : Pattern) (ha : d169053 p = 1) (hb : d169293 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169048 q = 1) (hb : d169288 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d169048, d169288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169048, d169288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35843 q ha hb
  have h2 (q : Pattern) (ha : d169049 q = 1) (hb : d169289 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d169049, d169289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169049, d169289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169050 q = 1) (hb : d169290 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d169050, d169290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169050, d169290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169051 q = 1) (hb : d169291 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d169051, d169291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169051, d169291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169052 q = 1) (hb : d169292 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d169052, d169292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169052, d169292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169053 q = 1) (hb : d169293 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d169053, d169293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169053, d169293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35845 (p : Pattern) (ha : d168731 p = 1) (hb : d169302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167036 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167042 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d167063 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d168726 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168727 q = 1) (hb : d169298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168727, d169298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168727, d169298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d167082 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d168728 q = 1) (hb : d169299 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168728, d169299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d168728, d169299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168729 q = 1) (hb : d169300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168729, d169300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d168729, d169300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d168730 q = 1) (hb : d169301 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168730, d169301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168730, d169301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d168731 q = 1) (hb : d169302 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168731, d169302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168731, d169302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro35846 (p : Pattern) (ha : d168741 p = 1) (hb : d169307 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d167036 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167042 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d168726 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d168727 q = 1) (hb : d169298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168727, d169298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d168727, d169298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d167082 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d168728 q = 1) (hb : d169299 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168728, d169299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d168728, d169299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168729 q = 1) (hb : d169300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168729, d169300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168729, d169300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d168730 q = 1) (hb : d169301 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168730, d169301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168730, d169301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d167091 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d167095 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d167098 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d168736 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d168737 q = 1) (hb : d169303 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168737, d169303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d168737, d169303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d167104 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d168738 q = 1) (hb : d169304 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168738, d169304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d168738, d169304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d168739 q = 1) (hb : d169305 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168739, d169305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d168739, d169305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d168740 q = 1) (hb : d169306 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168740, d169306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d168740, d169306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d168741 q = 1) (hb : d169307 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d168741, d169307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d168741, d169307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro35847 (p : Pattern) (ha : d169060 p = 1) (hb : d169314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d168736 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168737 q = 1) (hb : d169303 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d168737, d169303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168737, d169303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167104 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d168738 q = 1) (hb : d169304 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d168738, d169304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d168738, d169304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d168739 q = 1) (hb : d169312 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d168739, d169312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168739, d169312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d168740 q = 1) (hb : d169313 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d168740, d169313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168740, d169313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d169060 q = 1) (hb : d169314 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d169060, d169314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169060, d169314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35848 (p : Pattern) (ha : d169071 p = 1) (hb : d169324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d167151 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d169066 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d169067 q = 1) (hb : d169320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d169067, d169320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169067, d169320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d167174 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d169068 q = 1) (hb : d169321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d169068, d169321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169068, d169321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169069 q = 1) (hb : d169322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d169069, d169322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169069, d169322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169070 q = 1) (hb : d169323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d169070, d169323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169070, d169323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d169071 q = 1) (hb : d169324 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d169071, d169324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169071, d169324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35849 (p : Pattern) (ha : d169077 p = 1) (hb : d169330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d167030 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d168742 q = 1) (hb : d169308 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d168742, d169308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35845 q ha hb
    | true =>
      simp only [d168742, d169308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35846 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d167116 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d168743 q = 1) (hb : d169309 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d168743, d169309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168743, d169309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d169058 q = 1) (hb : d169310 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d169058, d169310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169058, d169310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169059 q = 1) (hb : d169311 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d169059, d169311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169059, d169311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169061 q = 1) (hb : d169315 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d169061, d169315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169061, d169315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35847 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d136711 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d169062 q = 1) (hb : d169316 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d169062, d169316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d169062, d169316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169063 q = 1) (hb : d169317 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d169063, d169317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d169063, d169317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d169064 q = 1) (hb : d169318 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d169064, d169318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d169064, d169318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d169065 q = 1) (hb : d169319 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d169065, d169319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d169065, d169319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d169072 q = 1) (hb : d169325 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d169072, d169325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169072, d169325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35848 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d136798 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d169073 q = 1) (hb : d169326 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d169073, d169326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d169073, d169326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d169074 q = 1) (hb : d169327 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d169074, d169327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d169074, d169327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d169075 q = 1) (hb : d169328 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d169075, d169328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d169075, d169328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d169076 q = 1) (hb : d169329 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d169076, d169329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d169076, d169329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d169077 q = 1) (hb : d169330 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d169077, d169330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d169077, d169330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro35850 (p : Pattern) (ha : d169083 p = 1) (hb : d169336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169078 q = 1) (hb : d169331 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d169078, d169331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169078, d169331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35849 q ha hb
  have h2 (q : Pattern) (ha : d169079 q = 1) (hb : d169332 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d169079, d169332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169079, d169332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d169080 q = 1) (hb : d169333 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d169080, d169333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169080, d169333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169081 q = 1) (hb : d169334 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d169081, d169334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169081, d169334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d169082 q = 1) (hb : d169335 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d169082, d169335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169082, d169335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169083 q = 1) (hb : d169336 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d169083, d169336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d169083, d169336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35851 (p : Pattern) (ha : d169089 p = 1) (hb : d169342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d168970 q = 1) (hb : d169171 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d168970, d169171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35820 q ha hb
    | true =>
      simp only [d168970, d169171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35826 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d168997 q = 1) (hb : d169211 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d168997, d169211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d168997, d169211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35832 q ha hb
  have h3 (q : Pattern) (ha : d168998 q = 1) (hb : d169212 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d168998, d169212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d168998, d169212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d169025 q = 1) (hb : d169252 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d169025, d169252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169025, d169252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35838 q ha hb
  have h5 (q : Pattern) (ha : d169026 q = 1) (hb : d169253 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d169026, d169253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169026, d169253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d169027 q = 1) (hb : d169254 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d169027, d169254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169027, d169254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d169054 q = 1) (hb : d169294 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d169054, d169294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169054, d169294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35844 q ha hb
  have h8 (q : Pattern) (ha : d169055 q = 1) (hb : d169295 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d169055, d169295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169055, d169295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d169056 q = 1) (hb : d169296 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d169056, d169296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169056, d169296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d169057 q = 1) (hb : d169297 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d169057, d169297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d169057, d169297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d169084 q = 1) (hb : d169337 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d169084, d169337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169084, d169337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35850 q ha hb
  have h12 (q : Pattern) (ha : d169085 q = 1) (hb : d169338 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d169085, d169338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169085, d169338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d169086 q = 1) (hb : d169339 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d169086, d169339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169086, d169339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d169087 q = 1) (hb : d169340 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d169087, d169340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169087, d169340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d169088 q = 1) (hb : d169341 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d169088, d169341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d169088, d169341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d169089 q = 1) (hb : d169342 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d169089, d169342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d169089, d169342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro35852 (p : Pattern) (ha : d169095 p = 1) (hb : d169348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169090 q = 1) (hb : d169343 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d169090, d169343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35851 q ha hb
    | true =>
      simp only [d169090, d169343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d169091 q = 1) (hb : d169344 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d169091, d169344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169091, d169344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169092 q = 1) (hb : d169345 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d169092, d169345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d169092, d169345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d169093 q = 1) (hb : d169346 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d169093, d169346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169093, d169346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d169094 q = 1) (hb : d169347 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d169094, d169347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169094, d169347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d169095 q = 1) (hb : d169348 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d169095, d169348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d169095, d169348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35853 (p : Pattern) (ha : d169101 p = 1) (hb : d169354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169096 q = 1) (hb : d169349 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d169096, d169349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35852 q ha hb
    | true =>
      simp only [d169096, d169349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d169097 q = 1) (hb : d169350 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d169097, d169350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169097, d169350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169098 q = 1) (hb : d169351 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d169098, d169351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d169098, d169351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d169099 q = 1) (hb : d169352 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d169099, d169352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169099, d169352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d169100 q = 1) (hb : d169353 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d169100, d169353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169100, d169353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d169101 q = 1) (hb : d169354 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d169101, d169354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d169101, d169354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35854 (p : Pattern) (ha : d169107 p = 1) (hb : d169360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169102 q = 1) (hb : d169355 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d169102, d169355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35853 q ha hb
    | true =>
      simp only [d169102, d169355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d169103 q = 1) (hb : d169356 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d169103, d169356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169103, d169356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169104 q = 1) (hb : d169357 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d169104, d169357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d169104, d169357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d169105 q = 1) (hb : d169358 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d169105, d169358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169105, d169358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d169106 q = 1) (hb : d169359 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d169106, d169359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169106, d169359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d169107 q = 1) (hb : d169360 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d169107, d169360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d169107, d169360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35855 (p : Pattern) (ha : d169113 p = 1) (hb : d169366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169108 q = 1) (hb : d169361 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d169108, d169361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35854 q ha hb
    | true =>
      simp only [d169108, d169361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d169109 q = 1) (hb : d169362 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d169109, d169362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169109, d169362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169110 q = 1) (hb : d169363 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d169110, d169363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d169110, d169363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d169111 q = 1) (hb : d169364 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d169111, d169364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169111, d169364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d169112 q = 1) (hb : d169365 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d169112, d169365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169112, d169365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d169113 q = 1) (hb : d169366 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d169113, d169366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d169113, d169366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35856 (p : Pattern) (ha : d169119 p = 1) (hb : d169372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169114 q = 1) (hb : d169367 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d169114, d169367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35855 q ha hb
    | true =>
      simp only [d169114, d169367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d169115 q = 1) (hb : d169368 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d169115, d169368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169115, d169368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169116 q = 1) (hb : d169369 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d169116, d169369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d169116, d169369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d169117 q = 1) (hb : d169370 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d169117, d169370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169117, d169370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d169118 q = 1) (hb : d169371 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d169118, d169371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169118, d169371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d169119 q = 1) (hb : d169372 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d169119, d169372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d169119, d169372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35857 (p : Pattern) (ha : d169125 p = 1) (hb : d169378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169120 q = 1) (hb : d169373 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d169120, d169373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35856 q ha hb
    | true =>
      simp only [d169120, d169373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d169121 q = 1) (hb : d169374 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d169121, d169374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169121, d169374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169122 q = 1) (hb : d169375 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d169122, d169375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d169122, d169375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d169123 q = 1) (hb : d169376 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d169123, d169376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169123, d169376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d169124 q = 1) (hb : d169377 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d169124, d169377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169124, d169377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d169125 q = 1) (hb : d169378 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d169125, d169378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d169125, d169378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35858 (p : Pattern) (ha : d169131 p = 1) (hb : d169384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d169126 q = 1) (hb : d169379 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d169126, d169379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35857 q ha hb
    | true =>
      simp only [d169126, d169379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d169127 q = 1) (hb : d169380 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d169127, d169380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d169127, d169380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d169128 q = 1) (hb : d169381 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d169128, d169381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d169128, d169381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d169129 q = 1) (hb : d169382 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d169129, d169382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d169129, d169382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d169130 q = 1) (hb : d169383 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d169130, d169383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d169130, d169383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d169131 q = 1) (hb : d169384 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d169131, d169384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d169131, d169384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35859 (p : Pattern) (ha : d36 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d32 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d33 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d36 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d36, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro35860 (p : Pattern) (ha : d42 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35861 (p : Pattern) (ha : d48 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d48 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d48, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35862 (p : Pattern) (ha : d49 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d41 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d49 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d49, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35863 (p : Pattern) (ha : d55 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35862 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d51 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d52 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d55 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d55, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35864 (p : Pattern) (ha : d60 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35862 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d52 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d52, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35865 (p : Pattern) (ha : d77 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d75 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d76 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d76, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d77 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d77, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro35866 (p : Pattern) (ha : d83 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d78 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35865 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d79 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d81 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d81, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35867 (p : Pattern) (ha : d89 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35866 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d86 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d86, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d87 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d87, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d89 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35868 (p : Pattern) (ha : d95 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d56 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35861 q ha hb
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35863 q ha hb
  have h2 (q : Pattern) (ha : d57 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d58 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d59 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35864 q ha hb
  have h6 (q : Pattern) (ha : d62 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d63 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d64 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d65 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d90 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d90, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35867 q ha hb
  have h11 (q : Pattern) (ha : d91 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d91, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d92 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d93 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d93, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d95 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d95, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35869 (p : Pattern) (ha : d104 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d104 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35870 (p : Pattern) (ha : d111 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d50 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35862 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d107 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d110 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d111 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35871 (p : Pattern) (ha : d213 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d213 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35872 (p : Pattern) (ha : d116 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35873 (p : Pattern) (ha : d123 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35874 (p : Pattern) (ha : d13987 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13983 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13984 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d32 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d33 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d13985 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13986 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13987 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro35875 (p : Pattern) (ha : d13993 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35874 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13992 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13993 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35876 (p : Pattern) (ha : d125417 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35872 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35873 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13994 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35875 q ha hb
    | true =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
  have h9 (q : Pattern) (ha : d125413 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125414 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125415 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125416 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125417 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35877 (p : Pattern) (ha : d194 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d40 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d194 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35878 (p : Pattern) (ha : d199 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d39 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d121 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35879 (p : Pattern) (ha : d14000 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35874 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13992 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14000 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35880 (p : Pattern) (ha : d125422 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35872 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35873 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13994 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35875 q ha hb
    | true =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
  have h9 (q : Pattern) (ha : d125413 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125414 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125415 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125416 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35877 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35878 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14001 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35879 q ha hb
    | true =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35862 q ha hb
  have h23 (q : Pattern) (ha : d125418 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35862 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125419 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125420 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125421 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125422 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro35881 (p : Pattern) (ha : d125429 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14001 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35879 q ha hb
    | true =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35862 q ha hb
  have h2 (q : Pattern) (ha : d125418 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35862 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125419 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125427 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125428 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125429 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35882 (p : Pattern) (ha : d14026 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14023 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d73 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14024 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14025 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14026 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro35883 (p : Pattern) (ha : d14032 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14027 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35882 q ha hb
    | true =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14028 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35865 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14029 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14030 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14031 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14032 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35884 (p : Pattern) (ha : d125439 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14033 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35883 q ha hb
    | true =>
      simp only [d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35866 q ha hb
  have h2 (q : Pattern) (ha : d125435 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35866 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125436 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125437 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125438 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125439 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35885 (p : Pattern) (ha : d125445 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35869 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35869 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35870 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125423 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35876 q ha hb
    | true =>
      simp only [d125423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35880 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35871 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d125424 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125425 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125426 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125430 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35881 q ha hb
  have h12 (q : Pattern) (ha : d125431 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d125432 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d125433 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125434 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125440 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35884 q ha hb
  have h17 (q : Pattern) (ha : d125441 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d125442 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d125443 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d125444 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125445 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro35886 (p : Pattern) (ha : d406 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d50 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35862 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d107 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d108 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d110 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d406 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35887 (p : Pattern) (ha : d462 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35866 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d458 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d459 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d460 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d461 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d462 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35888 (p : Pattern) (ha : d14054 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35875 q ha hb
    | true =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14054 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35889 (p : Pattern) (ha : d14061 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35875 q ha hb
    | true =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14001 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35879 q ha hb
    | true =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35862 q ha hb
  have h7 (q : Pattern) (ha : d14057 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14058 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14059 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14060 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14061 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35890 (p : Pattern) (ha : d14141 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13994 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35875 q ha hb
    | true =>
      simp only [d13994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
  have h2 (q : Pattern) (ha : d14050 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14051 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14052 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14053 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35860 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14141 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35891 (p : Pattern) (ha : d14066 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35874 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14065 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14066 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35892 (p : Pattern) (ha : d14073 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35874 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14071 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14072 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14073 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35893 (p : Pattern) (ha : d14085 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14081 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14082 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13983 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13984 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14083 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d32 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d33 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d13985 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14084 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14085 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35894 (p : Pattern) (ha : d14091 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35893 q ha hb
    | true =>
      simp only [d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35874 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14091 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35895 (p : Pattern) (ha : d14112 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35874 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14112 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35896 (p : Pattern) (ha : d125455 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14067 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35891 q ha hb
    | true =>
      simp only [d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35872 q ha hb
  have h2 (q : Pattern) (ha : d14068 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14069 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14070 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14074 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35892 q ha hb
    | true =>
      simp only [d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35873 q ha hb
  have h6 (q : Pattern) (ha : d14075 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14076 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14092 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35894 q ha hb
    | true =>
      simp only [d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35875 q ha hb
  have h9 (q : Pattern) (ha : d125451 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14113 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35895 q ha hb
    | true =>
      simp only [d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14114 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125452 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125453 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125454 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125455 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35897 (p : Pattern) (ha : d14119 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35874 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13991 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14065 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14119 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35898 (p : Pattern) (ha : d14124 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35874 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35859 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13990 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14071 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14072 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14124 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35899 (p : Pattern) (ha : d14128 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35893 q ha hb
    | true =>
      simp only [d14086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35874 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14128 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35900 (p : Pattern) (ha : d14133 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35874 q ha hb
    | true =>
      simp only [d13988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14133 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35901 (p : Pattern) (ha : d125460 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14067 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35891 q ha hb
    | true =>
      simp only [d14067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35872 q ha hb
  have h2 (q : Pattern) (ha : d14068 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14069 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14070 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14074 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35892 q ha hb
    | true =>
      simp only [d14074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35873 q ha hb
  have h6 (q : Pattern) (ha : d14075 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14076 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14092 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35894 q ha hb
    | true =>
      simp only [d14092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35875 q ha hb
  have h9 (q : Pattern) (ha : d125451 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14113 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35895 q ha hb
    | true =>
      simp only [d14113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14114 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125452 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125453 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125454 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14120 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35897 q ha hb
    | true =>
      simp only [d14120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35877 q ha hb
  have h16 (q : Pattern) (ha : d14121 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14122 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14123 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14125 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35898 q ha hb
    | true =>
      simp only [d14125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35878 q ha hb
  have h20 (q : Pattern) (ha : d14126 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14127 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14129 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35899 q ha hb
    | true =>
      simp only [d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35879 q ha hb
  have h23 (q : Pattern) (ha : d125456 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14134 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35900 q ha hb
    | true =>
      simp only [d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14135 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125457 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125458 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125459 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125460 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro35902 (p : Pattern) (ha : d125467 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14129 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35899 q ha hb
    | true =>
      simp only [d14129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35879 q ha hb
  have h2 (q : Pattern) (ha : d125456 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14134 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35900 q ha hb
    | true =>
      simp only [d14134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14135 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125457 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125465 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125466 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125467 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35903 (p : Pattern) (ha : d14162 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14158 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14159 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14022 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14023 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14160 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d73 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d14024 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14161 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14162 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35904 (p : Pattern) (ha : d14168 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14163 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35903 q ha hb
    | true =>
      simp only [d14163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14164 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14027 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35882 q ha hb
    | true =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14028 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14165 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14166 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14167 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14168 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35905 (p : Pattern) (ha : d14189 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14027 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35882 q ha hb
    | true =>
      simp only [d14027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14028 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14186 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14187 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14188 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14189 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35906 (p : Pattern) (ha : d125477 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14169 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35904 q ha hb
    | true =>
      simp only [d14169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35883 q ha hb
  have h2 (q : Pattern) (ha : d125473 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14190 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35905 q ha hb
    | true =>
      simp only [d14190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14191 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125474 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125475 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125476 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125477 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35907 (p : Pattern) (ha : d125483 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14055 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35888 q ha hb
  have h2 (q : Pattern) (ha : d14056 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14062 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35888 q ha hb
    | true =>
      simp only [d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35889 q ha hb
  have h4 (q : Pattern) (ha : d14063 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14064 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125461 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35896 q ha hb
    | true =>
      simp only [d125461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35901 q ha hb
  have h7 (q : Pattern) (ha : d14142 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35890 q ha hb
    | true =>
      simp only [d14142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35870 q ha hb
  have h8 (q : Pattern) (ha : d125462 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125463 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125464 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125468 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35902 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35886 q ha hb
  have h13 (q : Pattern) (ha : d125469 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125470 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125471 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125472 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35906 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35887 q ha hb
  have h19 (q : Pattern) (ha : d125479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125480 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125481 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35908 (p : Pattern) (ha : d125489 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35868 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125446 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35885 q ha hb
  have h6 (q : Pattern) (ha : d125447 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125448 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125449 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125450 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125484 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35907 q ha hb
  have h11 (q : Pattern) (ha : d125485 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d125486 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125487 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125488 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125489 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35909 (p : Pattern) (ha : d14210 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14081 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14082 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13983 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13984 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14083 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14208 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14209 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14210 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro35910 (p : Pattern) (ha : d14214 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13983 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13984 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14208 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14213 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d14214 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro35911 (p : Pattern) (ha : d14220 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35909 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14219 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14220 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35912 (p : Pattern) (ha : d14224 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14223 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14224 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35913 (p : Pattern) (ha : d14230 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35911 q ha hb
    | true =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35912 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14230 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35914 (p : Pattern) (ha : d14233 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35909 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14219 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14233 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35915 (p : Pattern) (ha : d14234 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14223 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14234 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35916 (p : Pattern) (ha : d14240 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35911 q ha hb
    | true =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35912 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14235 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35914 q ha hb
    | true =>
      simp only [d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35915 q ha hb
  have h7 (q : Pattern) (ha : d14236 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14237 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14238 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14239 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14240 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35917 (p : Pattern) (ha : d14349 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35911 q ha hb
    | true =>
      simp only [d14225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35912 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14344 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35912 q ha hb
    | true =>
      simp only [d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14345 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14346 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14347 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14348 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14349 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35918 (p : Pattern) (ha : d14355 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14344 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35912 q ha hb
    | true =>
      simp only [d14344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14345 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14346 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14347 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14348 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14350 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35915 q ha hb
    | true =>
      simp only [d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14351 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14352 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14353 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14354 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14355 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35919 (p : Pattern) (ha : d14364 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14350 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35915 q ha hb
    | true =>
      simp only [d14350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14351 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14352 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14353 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14354 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14364 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35920 (p : Pattern) (ha : d14395 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14023 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14385 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14394 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d14395 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro35921 (p : Pattern) (ha : d14447 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14396 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35920 q ha hb
    | true =>
      simp only [d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14397 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14444 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14445 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14446 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14447 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35922 (p : Pattern) (ha : d14453 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14448 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35921 q ha hb
    | true =>
      simp only [d14448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14449 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14450 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14451 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14452 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14453 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35923 (p : Pattern) (ha : d14245 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35909 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14244 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14245 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35924 (p : Pattern) (ha : d14247 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14246 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14247 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35925 (p : Pattern) (ha : d14254 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35909 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14252 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14253 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14254 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35926 (p : Pattern) (ha : d14257 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14255 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14256 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14257 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35927 (p : Pattern) (ha : d14273 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14266 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14266, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14266, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14269 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14270 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14270, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14270, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14271 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14081 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14082 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13983 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13984 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d14083 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14272 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14273 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro35928 (p : Pattern) (ha : d14279 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14274 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35927 q ha hb
    | true =>
      simp only [d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14275 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35909 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14276 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14277 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14278 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14279 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35929 (p : Pattern) (ha : d14312 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35909 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14309 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14310 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14311 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14312 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35930 (p : Pattern) (ha : d125494 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14248 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35923 q ha hb
    | true =>
      simp only [d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35924 q ha hb
  have h2 (q : Pattern) (ha : d14249 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14250 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14251 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14258 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35925 q ha hb
    | true =>
      simp only [d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35926 q ha hb
  have h6 (q : Pattern) (ha : d14259 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14260 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14280 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35928 q ha hb
    | true =>
      simp only [d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35911 q ha hb
  have h9 (q : Pattern) (ha : d125490 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14313 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35929 q ha hb
    | true =>
      simp only [d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14314 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125491 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125492 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125493 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125494 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35931 (p : Pattern) (ha : d14319 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35909 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14244 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14319 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35932 (p : Pattern) (ha : d14320 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14246 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14320 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35933 (p : Pattern) (ha : d14325 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35909 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14252 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14253 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14325 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35934 (p : Pattern) (ha : d14326 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35910 q ha hb
    | true =>
      simp only [d14215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14255 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14256 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14326 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35935 (p : Pattern) (ha : d14330 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14274 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35927 q ha hb
    | true =>
      simp only [d14274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14275 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35909 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14276 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14277 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14278 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14330 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35936 (p : Pattern) (ha : d14336 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35909 q ha hb
    | true =>
      simp only [d14211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14309 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14310 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14311 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14336 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35937 (p : Pattern) (ha : d125499 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14248 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35923 q ha hb
    | true =>
      simp only [d14248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35924 q ha hb
  have h2 (q : Pattern) (ha : d14249 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14250 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14251 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14258 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35925 q ha hb
    | true =>
      simp only [d14258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35926 q ha hb
  have h6 (q : Pattern) (ha : d14259 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14260 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14280 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35928 q ha hb
    | true =>
      simp only [d14280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35911 q ha hb
  have h9 (q : Pattern) (ha : d125490 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14313 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35929 q ha hb
    | true =>
      simp only [d14313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14314 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125491 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125492 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125493 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14321 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35931 q ha hb
    | true =>
      simp only [d14321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35932 q ha hb
  have h16 (q : Pattern) (ha : d14322 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14323 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14324 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14327 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35933 q ha hb
    | true =>
      simp only [d14327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35934 q ha hb
  have h20 (q : Pattern) (ha : d14328 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14329 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14331 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35935 q ha hb
    | true =>
      simp only [d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35914 q ha hb
  have h23 (q : Pattern) (ha : d125495 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14337 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35936 q ha hb
    | true =>
      simp only [d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14338 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125496 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125497 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125498 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125499 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro35938 (p : Pattern) (ha : d125506 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14331 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35935 q ha hb
    | true =>
      simp only [d14331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35914 q ha hb
  have h2 (q : Pattern) (ha : d125495 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14337 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35936 q ha hb
    | true =>
      simp only [d14337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14338 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125496 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125504 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125505 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125506 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35939 (p : Pattern) (ha : d14382 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14375 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14375, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14375, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14378 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14379 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14379, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14379, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14380 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14158 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14159 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14022 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14023 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d14160 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14381 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14382 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro35940 (p : Pattern) (ha : d14387 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14158 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14159 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14022 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14023 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14160 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14385 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14386 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14387 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro35941 (p : Pattern) (ha : d14393 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14383 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35939 q ha hb
    | true =>
      simp only [d14383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14384 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14388 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35940 q ha hb
    | true =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14389 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14390 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14391 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14392 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14393 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35942 (p : Pattern) (ha : d14401 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14388 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35940 q ha hb
    | true =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14389 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14396 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35920 q ha hb
    | true =>
      simp only [d14396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14397 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14398 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14399 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14400 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14401 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35943 (p : Pattern) (ha : d14436 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14388 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35940 q ha hb
    | true =>
      simp only [d14388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14389 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14433 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14434 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14435 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14436 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35944 (p : Pattern) (ha : d125516 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14402 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35941 q ha hb
    | true =>
      simp only [d14402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35942 q ha hb
  have h2 (q : Pattern) (ha : d125512 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14437 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35943 q ha hb
    | true =>
      simp only [d14437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14438 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125513 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125514 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125515 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125516 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35945 (p : Pattern) (ha : d125522 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14231 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35913 q ha hb
  have h2 (q : Pattern) (ha : d14232 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14241 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35913 q ha hb
    | true =>
      simp only [d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35916 q ha hb
  have h4 (q : Pattern) (ha : d14242 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14243 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125500 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35930 q ha hb
    | true =>
      simp only [d125500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35937 q ha hb
  have h7 (q : Pattern) (ha : d14356 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35917 q ha hb
    | true =>
      simp only [d14356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35918 q ha hb
  have h8 (q : Pattern) (ha : d125501 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125502 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125503 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125507 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35938 q ha hb
  have h12 (q : Pattern) (ha : d14365 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35919 q ha hb
  have h13 (q : Pattern) (ha : d125508 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125509 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125510 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125511 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125517 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35944 q ha hb
  have h18 (q : Pattern) (ha : d14454 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35922 q ha hb
  have h19 (q : Pattern) (ha : d125518 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125519 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125520 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125521 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125522 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35946 (p : Pattern) (ha : d125528 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125523 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35945 q ha hb
  have h2 (q : Pattern) (ha : d125524 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125525 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125526 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125527 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125528 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35947 (p : Pattern) (ha : d14477 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14469 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14470 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14470, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14473 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14474 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14475 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14476 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14477 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro35948 (p : Pattern) (ha : d14481 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14472 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14473 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14475 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14480 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d14481 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro35949 (p : Pattern) (ha : d14487 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35947 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14486 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14487 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35950 (p : Pattern) (ha : d14491 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14490 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14491 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35951 (p : Pattern) (ha : d14497 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35949 q ha hb
    | true =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35950 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14497 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35952 (p : Pattern) (ha : d14500 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35947 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14486 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14500 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35953 (p : Pattern) (ha : d14501 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14490 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14501 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35954 (p : Pattern) (ha : d14507 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35949 q ha hb
    | true =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35950 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14502 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35952 q ha hb
    | true =>
      simp only [d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35953 q ha hb
  have h7 (q : Pattern) (ha : d14503 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14504 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14505 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14506 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14507 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35955 (p : Pattern) (ha : d14622 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35949 q ha hb
    | true =>
      simp only [d14492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35950 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14617 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35950 q ha hb
    | true =>
      simp only [d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14618 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14619 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14620 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14621 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14622 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35956 (p : Pattern) (ha : d14628 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14617 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35950 q ha hb
    | true =>
      simp only [d14617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14618 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14619 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14620 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14621 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14623 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35953 q ha hb
    | true =>
      simp only [d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14624 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14625 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14626 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14627 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14628 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35957 (p : Pattern) (ha : d14637 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14623 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35953 q ha hb
    | true =>
      simp only [d14623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14624 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14625 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14626 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14627 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14637 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35958 (p : Pattern) (ha : d14680 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14663 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14664 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14670 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14679 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d14680 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro35959 (p : Pattern) (ha : d14736 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14681 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35958 q ha hb
    | true =>
      simp only [d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14682 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14733 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14734 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14735 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14736 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35960 (p : Pattern) (ha : d14742 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14737 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35959 q ha hb
    | true =>
      simp only [d14737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14738 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14739 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14740 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14741 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14742 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35961 (p : Pattern) (ha : d14512 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35947 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14511 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14512 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35962 (p : Pattern) (ha : d14514 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14513 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14514 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35963 (p : Pattern) (ha : d14521 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35947 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14519 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14520 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14521 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35964 (p : Pattern) (ha : d14524 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14522 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14523 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14524 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35965 (p : Pattern) (ha : d14542 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14534 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14535 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14535, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14535, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14538 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14539 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14539, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14539, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14540 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14469 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14470 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14470, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14473 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d14474 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14541 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14542 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro35966 (p : Pattern) (ha : d14548 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14543 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35965 q ha hb
    | true =>
      simp only [d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14544 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35947 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14545 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14546 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14547 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14548 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35967 (p : Pattern) (ha : d14585 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35947 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14582 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14583 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14584 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14585 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35968 (p : Pattern) (ha : d125534 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14515 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35961 q ha hb
    | true =>
      simp only [d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35962 q ha hb
  have h2 (q : Pattern) (ha : d14516 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14517 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14518 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14525 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35963 q ha hb
    | true =>
      simp only [d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35964 q ha hb
  have h6 (q : Pattern) (ha : d14526 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14527 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14549 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35966 q ha hb
    | true =>
      simp only [d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35949 q ha hb
  have h9 (q : Pattern) (ha : d125530 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14586 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35967 q ha hb
    | true =>
      simp only [d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14587 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125531 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125532 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125533 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125534 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35969 (p : Pattern) (ha : d14592 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35947 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14511 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14592 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35970 (p : Pattern) (ha : d14593 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14513 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14593 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35971 (p : Pattern) (ha : d14598 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35947 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14519 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14520 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14598 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35972 (p : Pattern) (ha : d14599 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35948 q ha hb
    | true =>
      simp only [d14482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14522 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14523 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14599 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35973 (p : Pattern) (ha : d14603 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14543 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35965 q ha hb
    | true =>
      simp only [d14543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14544 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35947 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14545 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14546 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14547 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14603 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35974 (p : Pattern) (ha : d14609 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35947 q ha hb
    | true =>
      simp only [d14478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14582 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14583 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14584 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14609 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35975 (p : Pattern) (ha : d125539 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14515 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35961 q ha hb
    | true =>
      simp only [d14515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35962 q ha hb
  have h2 (q : Pattern) (ha : d14516 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14517 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14518 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14525 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35963 q ha hb
    | true =>
      simp only [d14525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35964 q ha hb
  have h6 (q : Pattern) (ha : d14526 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14527 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14549 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35966 q ha hb
    | true =>
      simp only [d14549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35949 q ha hb
  have h9 (q : Pattern) (ha : d125530 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14586 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35967 q ha hb
    | true =>
      simp only [d14586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14587 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125531 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125532 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125533 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14594 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35969 q ha hb
    | true =>
      simp only [d14594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35970 q ha hb
  have h16 (q : Pattern) (ha : d14595 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14596 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14597 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14600 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35971 q ha hb
    | true =>
      simp only [d14600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35972 q ha hb
  have h20 (q : Pattern) (ha : d14601 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14602 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14604 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35973 q ha hb
    | true =>
      simp only [d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35952 q ha hb
  have h23 (q : Pattern) (ha : d125535 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14610 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35974 q ha hb
    | true =>
      simp only [d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14611 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125536 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125537 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125538 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125539 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro35976 (p : Pattern) (ha : d125546 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14604 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35973 q ha hb
    | true =>
      simp only [d14604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35952 q ha hb
  have h2 (q : Pattern) (ha : d125535 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14610 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35974 q ha hb
    | true =>
      simp only [d14610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14611 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125536 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125544 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125545 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125546 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35977 (p : Pattern) (ha : d14667 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14652 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14652, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14652, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14655 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14656 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14656, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14656, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14657 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14660 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14661 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14661, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14663 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14664 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d14665 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14666 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14667 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro35978 (p : Pattern) (ha : d14672 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14660 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14661 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14661, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14663 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14664 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14665 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14670 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14671 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14672 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro35979 (p : Pattern) (ha : d14678 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14668 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35977 q ha hb
    | true =>
      simp only [d14668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14669 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14673 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35978 q ha hb
    | true =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14674 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14675 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14676 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14677 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14678 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35980 (p : Pattern) (ha : d14686 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14673 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35978 q ha hb
    | true =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14674 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14681 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35958 q ha hb
    | true =>
      simp only [d14681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14682 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14683 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14684 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14685 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14686 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35981 (p : Pattern) (ha : d14725 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14673 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35978 q ha hb
    | true =>
      simp only [d14673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14674 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14722 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14723 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14724 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14725 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35982 (p : Pattern) (ha : d125556 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14687 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35979 q ha hb
    | true =>
      simp only [d14687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35980 q ha hb
  have h2 (q : Pattern) (ha : d125552 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14726 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35981 q ha hb
    | true =>
      simp only [d14726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14727 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125553 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125554 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125555 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125556 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35983 (p : Pattern) (ha : d125562 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14498 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35951 q ha hb
  have h2 (q : Pattern) (ha : d14499 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14508 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35951 q ha hb
    | true =>
      simp only [d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35954 q ha hb
  have h4 (q : Pattern) (ha : d14509 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14510 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125540 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35968 q ha hb
    | true =>
      simp only [d125540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35975 q ha hb
  have h7 (q : Pattern) (ha : d14629 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35955 q ha hb
    | true =>
      simp only [d14629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35956 q ha hb
  have h8 (q : Pattern) (ha : d125541 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125542 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125543 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125547 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35976 q ha hb
  have h12 (q : Pattern) (ha : d14638 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35957 q ha hb
  have h13 (q : Pattern) (ha : d125548 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125549 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125550 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125551 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125557 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35982 q ha hb
  have h18 (q : Pattern) (ha : d14743 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35960 q ha hb
  have h19 (q : Pattern) (ha : d125558 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125559 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125560 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125561 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125562 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35984 (p : Pattern) (ha : d125568 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125563 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35983 q ha hb
  have h2 (q : Pattern) (ha : d125564 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125565 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125566 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125567 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125568 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35985 (p : Pattern) (ha : d14784 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14768 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14769 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14775 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14776 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14777 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14780 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14781 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14781, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14781, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14782 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14783 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14784 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro35986 (p : Pattern) (ha : d14788 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14780 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14781 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14781, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14781, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14782 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14787 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d14788 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro35987 (p : Pattern) (ha : d14794 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35985 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14793 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14794 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35988 (p : Pattern) (ha : d14798 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14797 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14798 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35989 (p : Pattern) (ha : d14804 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14799 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35987 q ha hb
    | true =>
      simp only [d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35988 q ha hb
  have h2 (q : Pattern) (ha : d14800 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14801 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14802 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14803 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14804 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35990 (p : Pattern) (ha : d14807 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35985 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14793 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14807 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35991 (p : Pattern) (ha : d14808 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14797 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14808 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35992 (p : Pattern) (ha : d14814 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14799 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35987 q ha hb
    | true =>
      simp only [d14799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35988 q ha hb
  have h2 (q : Pattern) (ha : d14800 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14801 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14802 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14803 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14809 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35990 q ha hb
    | true =>
      simp only [d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35991 q ha hb
  have h7 (q : Pattern) (ha : d14810 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14811 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14812 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14813 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14814 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35993 (p : Pattern) (ha : d14855 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14768 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14769 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14775 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14776 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14777 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14853 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14854 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14855 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro35994 (p : Pattern) (ha : d14865 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14856 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35993 q ha hb
    | true =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14857 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14862 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14863 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14864 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14865 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35995 (p : Pattern) (ha : d14965 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14955 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35994 q ha hb
    | true =>
      simp only [d14955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35988 q ha hb
  have h2 (q : Pattern) (ha : d14956 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14957 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14958 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14959 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14960 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35988 q ha hb
    | true =>
      simp only [d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14961 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14962 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14963 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14964 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14965 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35996 (p : Pattern) (ha : d14971 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14960 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35988 q ha hb
    | true =>
      simp only [d14960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14961 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14962 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14963 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14964 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14966 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35991 q ha hb
    | true =>
      simp only [d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14967 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14968 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14969 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14970 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14971 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35997 (p : Pattern) (ha : d14980 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14966 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35991 q ha hb
    | true =>
      simp only [d14966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14967 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14968 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14969 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14970 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14980 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35998 (p : Pattern) (ha : d15048 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15045 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15046 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15047 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d15048 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro35999 (p : Pattern) (ha : d15128 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15049 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35998 q ha hb
    | true =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15050 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15125 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15126 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15127 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15128 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
