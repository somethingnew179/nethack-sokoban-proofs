import NetHack.Soko22Hazard87.AndIntroBlocks0294
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro73750 (p : Pattern) (ha : d53548 p = 1) (hb : d238631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53538 q = 1) (hb : d238621 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53538, d238621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73748 q ha hb
    | true =>
      simp only [d53538, d238621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53539 q = 1) (hb : d238622 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53539, d238622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53539, d238622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53543 q = 1) (hb : d238626 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53543, d238626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73749 q ha hb
    | true =>
      simp only [d53543, d238626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53544 q = 1) (hb : d238627 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53544, d238627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53544, d238627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53545 q = 1) (hb : d238628 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53545, d238628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53545, d238628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53546 q = 1) (hb : d238629 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53546, d238629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53546, d238629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53547 q = 1) (hb : d238630 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53547, d238630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53547, d238630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53548 q = 1) (hb : d238631 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53548, d238631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53548, d238631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73751 (p : Pattern) (ha : d53556 p = 1) (hb : d238639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53543 q = 1) (hb : d238626 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53543, d238626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73749 q ha hb
    | true =>
      simp only [d53543, d238626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53544 q = 1) (hb : d238627 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53544, d238627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53544, d238627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53551 q = 1) (hb : d238634 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d53551, d238634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73724 q ha hb
    | true =>
      simp only [d53551, d238634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53552 q = 1) (hb : d238635 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d53552, d238635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53552, d238635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53553 q = 1) (hb : d238636 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d53553, d238636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53553, d238636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53554 q = 1) (hb : d238637 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d53554, d238637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53554, d238637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53555 q = 1) (hb : d238638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d53555, d238638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53555, d238638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d53556 q = 1) (hb : d238639 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d53556, d238639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53556, d238639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro73752 (p : Pattern) (ha : d74496 p = 1) (hb : d238647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30408 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30408, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30408, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
  have h2 (q : Pattern) (ha : d30098 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73706 q ha hb
    | true =>
      simp only [d30098, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30409 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30409, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30409, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30099 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30099, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30410 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30410, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30410, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30411 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30411, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30411, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53511 q = 1) (hb : d238599 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53511, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53511, d238599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
  have h8 (q : Pattern) (ha : d53344 q = 1) (hb : d238442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73707 q ha hb
    | true =>
      simp only [d53344, d238442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d53512 q = 1) (hb : d238600 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53512, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53512, d238600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53345 q = 1) (hb : d238443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53345, d238443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d53513 q = 1) (hb : d238601 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53513, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53513, d238601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d53514 q = 1) (hb : d238602 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53514, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53514, d238602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d53515 q = 1) (hb : d238603 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53515, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53515, d238603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74491 q = 1) (hb : d238642 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74491, d238642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74491, d238642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70842 q ha hb
  have h15 (q : Pattern) (ha : d74447 q = 1) (hb : d238526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d74447, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70842 q ha hb
    | true =>
      simp only [d74447, d238526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74492 q = 1) (hb : d238643 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74492, d238643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74492, d238643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74448 q = 1) (hb : d238527 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d74448, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74448, d238527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d74493 q = 1) (hb : d238644 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d74493, d238644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74493, d238644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d74494 q = 1) (hb : d238645 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d74494, d238645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74494, d238645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d74495 q = 1) (hb : d238646 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d74495, d238646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74495, d238646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74496 q = 1) (hb : d238647 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d74496, d238647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74496, d238647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73753 (p : Pattern) (ha : d74503 p = 1) (hb : d238654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53522 q = 1) (hb : d238610 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53522, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73747 q ha hb
    | true =>
      simp only [d53522, d238610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73722 q ha hb
  have h2 (q : Pattern) (ha : d53523 q = 1) (hb : d238611 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53523, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53523, d238611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53524 q = 1) (hb : d238612 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53524, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53524, d238612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53532 q = 1) (hb : d238615 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d53532, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73722 q ha hb
    | true =>
      simp only [d53532, d238615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73723 q ha hb
  have h5 (q : Pattern) (ha : d53533 q = 1) (hb : d238616 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d53533, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53533, d238616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53534 q = 1) (hb : d238617 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d53534, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53534, d238617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53535 q = 1) (hb : d238618 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d53535, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53535, d238618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74498 q = 1) (hb : d238649 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d74498, d238649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73752 q ha hb
    | true =>
      simp only [d74498, d238649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70868 q ha hb
  have h9 (q : Pattern) (ha : d74499 q = 1) (hb : d238650 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d74499, d238650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74499, d238650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74500 q = 1) (hb : d238651 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74500, d238651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74500, d238651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74501 q = 1) (hb : d238652 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d74501, d238652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74501, d238652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d74502 q = 1) (hb : d238653 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d74502, d238653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74502, d238653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74503 q = 1) (hb : d238654 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d74503, d238654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74503, d238654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro73754 (p : Pattern) (ha : d74509 p = 1) (hb : d238660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74504 q = 1) (hb : d238655 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d74504, d238655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73753 q ha hb
    | true =>
      simp only [d74504, d238655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74505 q = 1) (hb : d238656 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d74505, d238656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74505, d238656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74506 q = 1) (hb : d238657 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d74506, d238657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74506, d238657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74507 q = 1) (hb : d238658 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d74507, d238658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74507, d238658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74508 q = 1) (hb : d238659 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d74508, d238659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74508, d238659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74509 q = 1) (hb : d238660 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d74509, d238660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74509, d238660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73755 (p : Pattern) (ha : d74515 p = 1) (hb : d238666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53557 q = 1) (hb : d238640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53557, d238640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73750 q ha hb
    | true =>
      simp only [d53557, d238640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73751 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53562 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53563 q = 1) (hb : d238641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53563, d238641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53563, d238641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d74510 q = 1) (hb : d238661 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d74510, d238661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73754 q ha hb
    | true =>
      simp only [d74510, d238661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74511 q = 1) (hb : d238662 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d74511, d238662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74511, d238662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74512 q = 1) (hb : d238663 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74512, d238663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74512, d238663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74513 q = 1) (hb : d238664 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74513, d238664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74513, d238664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74514 q = 1) (hb : d238665 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74514, d238665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74514, d238665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74515 q = 1) (hb : d238666 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74515, d238666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74515, d238666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro73756 (p : Pattern) (ha : d74521 p = 1) (hb : d238683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53392 q = 1) (hb : d238481 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53392, d238481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53392, d238481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73715 q ha hb
  have h2 (q : Pattern) (ha : d53393 q = 1) (hb : d238482 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53393, d238482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53393, d238482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53402 q = 1) (hb : d238491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53402, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73715 q ha hb
    | true =>
      simp only [d53402, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73718 q ha hb
  have h4 (q : Pattern) (ha : d53403 q = 1) (hb : d238492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53403, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53403, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53404 q = 1) (hb : d238493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53404, d238493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53404, d238493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74479 q = 1) (hb : d238572 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74479, d238572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73737 q ha hb
    | true =>
      simp only [d74479, d238572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73744 q ha hb
  have h7 (q : Pattern) (ha : d53482 q = 1) (hb : d238585 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53482, d238585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73719 q ha hb
    | true =>
      simp only [d53482, d238585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73720 q ha hb
  have h8 (q : Pattern) (ha : d74480 q = 1) (hb : d238586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74480, d238586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74480, d238586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74481 q = 1) (hb : d238587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74481, d238587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74481, d238587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d74482 q = 1) (hb : d238588 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74482, d238588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74482, d238588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74486 q = 1) (hb : d238592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74486, d238592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74486, d238592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73745 q ha hb
  have h12 (q : Pattern) (ha : d53491 q = 1) (hb : d238594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53491, d238594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53491, d238594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73721 q ha hb
  have h13 (q : Pattern) (ha : d74487 q = 1) (hb : d238595 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74487, d238595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74487, d238595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74488 q = 1) (hb : d238596 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74488, d238596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74488, d238596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d74489 q = 1) (hb : d238597 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74489, d238597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74489, d238597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d74490 q = 1) (hb : d238598 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74490, d238598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74490, d238598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74516 q = 1) (hb : d238667 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74516, d238667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74516, d238667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73755 q ha hb
  have h18 (q : Pattern) (ha : d53577 q = 1) (hb : d238678 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53577, d238678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53577, d238678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73726 q ha hb
  have h19 (q : Pattern) (ha : d74517 q = 1) (hb : d238679 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74517, d238679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74517, d238679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74518 q = 1) (hb : d238680 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74518, d238680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74518, d238680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d74519 q = 1) (hb : d238681 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74519, d238681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74519, d238681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d74520 q = 1) (hb : d238682 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74520, d238682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74520, d238682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d74521 q = 1) (hb : d238683 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74521, d238683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74521, d238683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro73757 (p : Pattern) (ha : d74527 p = 1) (hb : d238689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74522 q = 1) (hb : d238684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74522, d238684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74522, d238684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73756 q ha hb
  have h2 (q : Pattern) (ha : d74523 q = 1) (hb : d238685 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74523, d238685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74523, d238685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74524 q = 1) (hb : d238686 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74524, d238686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74524, d238686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74525 q = 1) (hb : d238687 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74525, d238687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74525, d238687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74526 q = 1) (hb : d238688 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74526, d238688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74526, d238688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74527 q = 1) (hb : d238689 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74527, d238689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74527, d238689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73758 (p : Pattern) (ha : d74533 p = 1) (hb : d238695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74173 q = 1) (hb : d211198 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74173, d211198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59524 q ha hb
    | true =>
      simp only [d74173, d211198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59553 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74258 q = 1) (hb : d211238 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74258, d211238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74258, d211238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59588 q ha hb
  have h3 (q : Pattern) (ha : d74259 q = 1) (hb : d211239 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74259, d211239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74259, d211239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74347 q = 1) (hb : d238212 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74347, d238212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74347, d238212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73650 q ha hb
  have h5 (q : Pattern) (ha : d74348 q = 1) (hb : d238213 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74348, d238213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74348, d238213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74349 q = 1) (hb : d238214 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74349, d238214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74349, d238214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74437 q = 1) (hb : d238435 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74437, d238435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74437, d238435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73704 q ha hb
  have h8 (q : Pattern) (ha : d74438 q = 1) (hb : d238436 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74438, d238436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74438, d238436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74439 q = 1) (hb : d238437 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74439, d238437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74439, d238437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74440 q = 1) (hb : d238438 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74440, d238438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74440, d238438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74528 q = 1) (hb : d238690 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74528, d238690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74528, d238690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73757 q ha hb
  have h12 (q : Pattern) (ha : d74529 q = 1) (hb : d238691 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74529, d238691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74529, d238691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74530 q = 1) (hb : d238692 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74530, d238692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74530, d238692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74531 q = 1) (hb : d238693 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74531, d238693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74531, d238693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74532 q = 1) (hb : d238694 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74532, d238694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74532, d238694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74533 q = 1) (hb : d238695 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74533, d238695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74533, d238695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro73759 (p : Pattern) (ha : d74539 p = 1) (hb : d238701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74534 q = 1) (hb : d238696 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74534, d238696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73758 q ha hb
    | true =>
      simp only [d74534, d238696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74535 q = 1) (hb : d238697 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74535, d238697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74535, d238697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74536 q = 1) (hb : d238698 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74536, d238698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74536, d238698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74537 q = 1) (hb : d238699 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74537, d238699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74537, d238699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74538 q = 1) (hb : d238700 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74538, d238700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74538, d238700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74539 q = 1) (hb : d238701 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74539, d238701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74539, d238701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73760 (p : Pattern) (ha : d74545 p = 1) (hb : d238707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74540 q = 1) (hb : d238702 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74540, d238702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73759 q ha hb
    | true =>
      simp only [d74540, d238702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74541 q = 1) (hb : d238703 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74541, d238703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74541, d238703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74542 q = 1) (hb : d238704 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74542, d238704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74542, d238704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74543 q = 1) (hb : d238705 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74543, d238705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74543, d238705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74544 q = 1) (hb : d238706 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74544, d238706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74544, d238706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74545 q = 1) (hb : d238707 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74545, d238707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74545, d238707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73761 (p : Pattern) (ha : d74551 p = 1) (hb : d238713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74546 q = 1) (hb : d238708 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74546, d238708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73760 q ha hb
    | true =>
      simp only [d74546, d238708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74547 q = 1) (hb : d238709 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74547, d238709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74547, d238709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74548 q = 1) (hb : d238710 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74548, d238710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74548, d238710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74549 q = 1) (hb : d238711 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74549, d238711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74549, d238711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74550 q = 1) (hb : d238712 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74550, d238712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74550, d238712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74551 q = 1) (hb : d238713 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74551, d238713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74551, d238713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73762 (p : Pattern) (ha : d74557 p = 1) (hb : d238719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74552 q = 1) (hb : d238714 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74552, d238714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73761 q ha hb
    | true =>
      simp only [d74552, d238714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74553 q = 1) (hb : d238715 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74553, d238715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74553, d238715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74554 q = 1) (hb : d238716 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74554, d238716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74554, d238716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74555 q = 1) (hb : d238717 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74555, d238717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74555, d238717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74556 q = 1) (hb : d238718 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74556, d238718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74556, d238718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74557 q = 1) (hb : d238719 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74557, d238719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74557, d238719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73763 (p : Pattern) (ha : d74563 p = 1) (hb : d238725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74558 q = 1) (hb : d238720 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74558, d238720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73762 q ha hb
    | true =>
      simp only [d74558, d238720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74559 q = 1) (hb : d238721 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74559, d238721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74559, d238721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74560 q = 1) (hb : d238722 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74560, d238722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74560, d238722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74561 q = 1) (hb : d238723 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74561, d238723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74561, d238723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74562 q = 1) (hb : d238724 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74562, d238724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74562, d238724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74563 q = 1) (hb : d238725 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74563, d238725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74563, d238725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73764 (p : Pattern) (ha : d74569 p = 1) (hb : d238731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74564 q = 1) (hb : d238726 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74564, d238726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73763 q ha hb
    | true =>
      simp only [d74564, d238726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74565 q = 1) (hb : d238727 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74565, d238727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74565, d238727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74566 q = 1) (hb : d238728 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74566, d238728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74566, d238728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74567 q = 1) (hb : d238729 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74567, d238729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74567, d238729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74568 q = 1) (hb : d238730 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74568, d238730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74568, d238730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74569 q = 1) (hb : d238731 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74569, d238731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74569, d238731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73765 (p : Pattern) (ha : d74575 p = 1) (hb : d238737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74570 q = 1) (hb : d238732 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74570, d238732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73764 q ha hb
    | true =>
      simp only [d74570, d238732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74571 q = 1) (hb : d238733 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74571, d238733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74571, d238733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74572 q = 1) (hb : d238734 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74572, d238734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74572, d238734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74573 q = 1) (hb : d238735 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74573, d238735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74573, d238735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74574 q = 1) (hb : d238736 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74574, d238736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74574, d238736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74575 q = 1) (hb : d238737 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74575, d238737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74575, d238737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73766 (p : Pattern) (ha : d236583 p = 1) (hb : d279926 p = 1) : d238846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236583 q = 1) (hb : d279921 q = 1) : d238841 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d236583, d279921, d238841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70907 q ha hb
    | true =>
      simp only [d236583, d279921, d238841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d236583 q = 1) (hb : d279922 q = 1) : d238842 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d279922, d238842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279922, d238842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d236583 q = 1) (hb : d279923 q = 1) : d238843 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d279923, d238843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279923, d238843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d236583 q = 1) (hb : d279924 q = 1) : d238844 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d279924, d238844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279924, d238844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d236583 q = 1) (hb : d279925 q = 1) : d238845 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d279925, d238845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279925, d238845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d236583 q = 1) (hb : d279926 q = 1) : d238846 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d279926, d238846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d279926, d238846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h7 p ha hb
theorem andIntro73767 (p : Pattern) (ha : d236583 p = 1) (hb : d279932 p = 1) : d238852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236583 q = 1) (hb : d279927 q = 1) : d238847 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d279927, d238847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73766 q ha hb
    | true =>
      simp only [d279927, d238847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d236583 q = 1) (hb : d279928 q = 1) : d238848 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d279928, d238848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279928, d238848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d236583 q = 1) (hb : d279929 q = 1) : d238849 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d279929, d238849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279929, d238849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d236583 q = 1) (hb : d279930 q = 1) : d238850 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d279930, d238850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279930, d238850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d236583 q = 1) (hb : d279931 q = 1) : d238851 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d279931, d238851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279931, d238851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d236583 q = 1) (hb : d279932 q = 1) : d238852 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d279932, d238852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279932, d238852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73768 (p : Pattern) (ha : d236583 p = 1) (hb : d279938 p = 1) : d238858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236583 q = 1) (hb : d279933 q = 1) : d238853 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d279933, d238853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73767 q ha hb
    | true =>
      simp only [d279933, d238853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d236583 q = 1) (hb : d279934 q = 1) : d238854 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d279934, d238854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279934, d238854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d236583 q = 1) (hb : d279935 q = 1) : d238855 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d279935, d238855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279935, d238855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d236583 q = 1) (hb : d279936 q = 1) : d238856 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d279936, d238856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279936, d238856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d236583 q = 1) (hb : d279937 q = 1) : d238857 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d279937, d238857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279937, d238857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d236583 q = 1) (hb : d279938 q = 1) : d238858 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d279938, d238858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279938, d238858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73769 (p : Pattern) (ha : d236583 p = 1) (hb : d279944 p = 1) : d238864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236583 q = 1) (hb : d279939 q = 1) : d238859 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d279939, d238859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73768 q ha hb
    | true =>
      simp only [d279939, d238859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d236583 q = 1) (hb : d279940 q = 1) : d238860 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d279940, d238860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279940, d238860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d236583 q = 1) (hb : d279941 q = 1) : d238861 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d279941, d238861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279941, d238861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d236583 q = 1) (hb : d279942 q = 1) : d238862 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d279942, d238862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279942, d238862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d236583 q = 1) (hb : d279943 q = 1) : d238863 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d279943, d238863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279943, d238863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d236583 q = 1) (hb : d279944 q = 1) : d238864 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d279944, d238864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279944, d238864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73770 (p : Pattern) (ha : d236583 p = 1) (hb : d279950 p = 1) : d238870 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d236583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d236583 q = 1) (hb : d279945 q = 1) : d238865 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d279945, d238865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73769 q ha hb
    | true =>
      simp only [d279945, d238865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d236583 q = 1) (hb : d279946 q = 1) : d238866 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d279946, d238866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d279946, d238866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d236583 q = 1) (hb : d279947 q = 1) : d238867 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d279947, d238867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d279947, d238867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d236583 q = 1) (hb : d279948 q = 1) : d238868 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d279948, d238868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d279948, d238868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d236583 q = 1) (hb : d279949 q = 1) : d238869 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d279949, d238869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d279949, d238869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d236583 q = 1) (hb : d279950 q = 1) : d238870 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d279950, d238870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d279950, d238870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73771 (p : Pattern) (ha : d74290 p = 1) (hb : d238020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d52744 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52744, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73605 q ha hb
    | true =>
      simp only [d52744, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73606 q ha hb
  have h5 (q : Pattern) (ha : d52810 q = 1) (hb : d238016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52810, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52810, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d74287 q = 1) (hb : d238017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74287, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74287, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d74288 q = 1) (hb : d238018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74288, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74288, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74289 q = 1) (hb : d238019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74289, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74289, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74290 q = 1) (hb : d238020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74290, d238020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74290, d238020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73772 (p : Pattern) (ha : d74297 p = 1) (hb : d238030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d52744 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52744, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73605 q ha hb
    | true =>
      simp only [d52744, d238015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73606 q ha hb
  have h4 (q : Pattern) (ha : d52810 q = 1) (hb : d238016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52810, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d52810, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74286 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74287 q = 1) (hb : d238017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74287, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74287, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74288 q = 1) (hb : d238018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74288, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74288, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74289 q = 1) (hb : d238019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74289, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74289, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d52754 q = 1) (hb : d238025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52754, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73608 q ha hb
    | true =>
      simp only [d52754, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73609 q ha hb
  have h13 (q : Pattern) (ha : d52830 q = 1) (hb : d238026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d52830, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74294 q = 1) (hb : d238027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74294, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74294, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74295 q = 1) (hb : d238028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74295, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d74295, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74296 q = 1) (hb : d238029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74296, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74296, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d74297 q = 1) (hb : d238030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74297, d238030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74297, d238030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73773 (p : Pattern) (ha : d74304 p = 1) (hb : d238740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52754 q = 1) (hb : d238025 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52754, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73608 q ha hb
    | true =>
      simp only [d52754, d238025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73609 q ha hb
  have h3 (q : Pattern) (ha : d52830 q = 1) (hb : d238026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52830, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52830, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74293 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74294 q = 1) (hb : d238027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74294, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74294, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74302 q = 1) (hb : d238028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74302, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74302, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74303 q = 1) (hb : d238029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74303, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74303, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74304 q = 1) (hb : d238740 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74304, d238740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74304, d238740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73774 (p : Pattern) (ha : d74334 p = 1) (hb : d238751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52930 q = 1) (hb : d238746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d52930, d238746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73644 q ha hb
    | true =>
      simp only [d52930, d238746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73617 q ha hb
  have h3 (q : Pattern) (ha : d52931 q = 1) (hb : d238747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d52931, d238747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52931, d238747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74330 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74331 q = 1) (hb : d238748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74331, d238748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74331, d238748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74332 q = 1) (hb : d238749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74332, d238749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74332, d238749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74333 q = 1) (hb : d238750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74333, d238750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74333, d238750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74334 q = 1) (hb : d238751 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74334, d238751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74334, d238751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73775 (p : Pattern) (ha : d74340 p = 1) (hb : d238757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74298 q = 1) (hb : d238031 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74298, d238031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73771 q ha hb
    | true =>
      simp only [d74298, d238031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73772 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d74299 q = 1) (hb : d238032 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74299, d238032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74299, d238032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74300 q = 1) (hb : d238738 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74300, d238738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74300, d238738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74301 q = 1) (hb : d238739 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74301, d238739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74301, d238739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74305 q = 1) (hb : d238741 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74305, d238741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74305, d238741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73773 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74306 q = 1) (hb : d238742 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74306, d238742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74306, d238742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74307 q = 1) (hb : d238743 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74307, d238743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74307, d238743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74308 q = 1) (hb : d238744 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74308, d238744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74308, d238744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74309 q = 1) (hb : d238745 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74309, d238745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74309, d238745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74335 q = 1) (hb : d238752 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74335, d238752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74335, d238752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73774 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74336 q = 1) (hb : d238753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74336, d238753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74336, d238753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74337 q = 1) (hb : d238754 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74337, d238754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74337, d238754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74338 q = 1) (hb : d238755 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74338, d238755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74338, d238755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74339 q = 1) (hb : d238756 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74339, d238756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74339, d238756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74340 q = 1) (hb : d238757 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74340, d238757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74340, d238757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73776 (p : Pattern) (ha : d74346 p = 1) (hb : d238763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74341 q = 1) (hb : d238758 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74341, d238758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74341, d238758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73775 q ha hb
  have h2 (q : Pattern) (ha : d74342 q = 1) (hb : d238759 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74342, d238759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74342, d238759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74343 q = 1) (hb : d238760 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74343, d238760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74343, d238760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74344 q = 1) (hb : d238761 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74344, d238761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74344, d238761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74345 q = 1) (hb : d238762 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74345, d238762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74345, d238762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74346 q = 1) (hb : d238763 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74346, d238763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74346, d238763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73777 (p : Pattern) (ha : d74380 p = 1) (hb : d238256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53065 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53065, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73659 q ha hb
    | true =>
      simp only [d53065, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73660 q ha hb
  have h5 (q : Pattern) (ha : d53125 q = 1) (hb : d238252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53125, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53125, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d74377 q = 1) (hb : d238253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74377, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74377, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d74378 q = 1) (hb : d238254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74378, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74378, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74379 q = 1) (hb : d238255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74379, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74379, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74380 q = 1) (hb : d238256 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74380, d238256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74380, d238256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73778 (p : Pattern) (ha : d74387 p = 1) (hb : d238266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53065 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53065, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73659 q ha hb
    | true =>
      simp only [d53065, d238251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73660 q ha hb
  have h4 (q : Pattern) (ha : d53125 q = 1) (hb : d238252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53125, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53125, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74376 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74377 q = 1) (hb : d238253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74377, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74377, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74378 q = 1) (hb : d238254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74378, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74378, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74379 q = 1) (hb : d238255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74379, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74379, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53075 q = 1) (hb : d238261 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53075, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73662 q ha hb
    | true =>
      simp only [d53075, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73663 q ha hb
  have h13 (q : Pattern) (ha : d53145 q = 1) (hb : d238262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d53145, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74384 q = 1) (hb : d238263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74384, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74384, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74385 q = 1) (hb : d238264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74385, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d74385, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74386 q = 1) (hb : d238265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74386, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74386, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d74387 q = 1) (hb : d238266 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74387, d238266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74387, d238266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73779 (p : Pattern) (ha : d74394 p = 1) (hb : d238769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53075 q = 1) (hb : d238261 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53075, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73662 q ha hb
    | true =>
      simp only [d53075, d238261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73663 q ha hb
  have h3 (q : Pattern) (ha : d53145 q = 1) (hb : d238262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53145, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53145, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74383 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74384 q = 1) (hb : d238263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74384, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74384, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74392 q = 1) (hb : d238264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74392, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74392, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74393 q = 1) (hb : d238265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74393, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74393, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74394 q = 1) (hb : d238769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74394, d238769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74394, d238769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73780 (p : Pattern) (ha : d74424 p = 1) (hb : d238780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53245 q = 1) (hb : d238775 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53245, d238775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73698 q ha hb
    | true =>
      simp only [d53245, d238775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73671 q ha hb
  have h3 (q : Pattern) (ha : d53246 q = 1) (hb : d238776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53246, d238776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53246, d238776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74420 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74421 q = 1) (hb : d238777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74421, d238777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74421, d238777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74422 q = 1) (hb : d238778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74422, d238778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74422, d238778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74423 q = 1) (hb : d238779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74423, d238779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74423, d238779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74424 q = 1) (hb : d238780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74424, d238780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74424, d238780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73781 (p : Pattern) (ha : d74430 p = 1) (hb : d238786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74388 q = 1) (hb : d238267 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74388, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73777 q ha hb
    | true =>
      simp only [d74388, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73778 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d74389 q = 1) (hb : d238268 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74389, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74389, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74390 q = 1) (hb : d238767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74390, d238767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74390, d238767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74391 q = 1) (hb : d238768 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74391, d238768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74391, d238768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74395 q = 1) (hb : d238770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74395, d238770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74395, d238770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73779 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74396 q = 1) (hb : d238771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74396, d238771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74396, d238771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74397 q = 1) (hb : d238772 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74397, d238772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74397, d238772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74398 q = 1) (hb : d238773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74398, d238773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74398, d238773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74399 q = 1) (hb : d238774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74399, d238774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74399, d238774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74425 q = 1) (hb : d238781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74425, d238781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74425, d238781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73780 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74426 q = 1) (hb : d238782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74426, d238782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74426, d238782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74427 q = 1) (hb : d238783 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74427, d238783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74427, d238783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74428 q = 1) (hb : d238784 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74428, d238784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74428, d238784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74429 q = 1) (hb : d238785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74429, d238785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74429, d238785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74430 q = 1) (hb : d238786 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74430, d238786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74430, d238786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73782 (p : Pattern) (ha : d74436 p = 1) (hb : d238792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74431 q = 1) (hb : d238787 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74431, d238787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74431, d238787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73781 q ha hb
  have h2 (q : Pattern) (ha : d74432 q = 1) (hb : d238788 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74432, d238788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74432, d238788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74433 q = 1) (hb : d238789 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74433, d238789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74433, d238789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74434 q = 1) (hb : d238790 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74434, d238790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74434, d238790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74435 q = 1) (hb : d238791 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74435, d238791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74435, d238791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74436 q = 1) (hb : d238792 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74436, d238792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74436, d238792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73783 (p : Pattern) (ha : d74471 p = 1) (hb : d238480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53386 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53386, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73713 q ha hb
    | true =>
      simp only [d53386, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73714 q ha hb
  have h5 (q : Pattern) (ha : d53442 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53442, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53442, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d74468 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74468, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74468, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d74469 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74469, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74469, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74470 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74470, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74470, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74471 q = 1) (hb : d238480 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74471, d238480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74471, d238480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73784 (p : Pattern) (ha : d74478 p = 1) (hb : d238490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53386 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53386, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73713 q ha hb
    | true =>
      simp only [d53386, d238475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73714 q ha hb
  have h4 (q : Pattern) (ha : d53442 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53442, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d53442, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74467 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74468 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74468, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74468, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74469 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74469, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74469, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74470 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74470, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74470, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d53396 q = 1) (hb : d238485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53396, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73716 q ha hb
    | true =>
      simp only [d53396, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73717 q ha hb
  have h13 (q : Pattern) (ha : d53462 q = 1) (hb : d238486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d53462, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74475 q = 1) (hb : d238487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74475, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74475, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74476 q = 1) (hb : d238488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74476, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d74476, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74477 q = 1) (hb : d238489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74477, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74477, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d74478 q = 1) (hb : d238490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74478, d238490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74478, d238490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73785 (p : Pattern) (ha : d74485 p = 1) (hb : d238799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53396 q = 1) (hb : d238485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53396, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73716 q ha hb
    | true =>
      simp only [d53396, d238485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73717 q ha hb
  have h3 (q : Pattern) (ha : d53462 q = 1) (hb : d238486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53462, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53462, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74474 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74475 q = 1) (hb : d238487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74475, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74475, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74483 q = 1) (hb : d238488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74483, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74483, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74484 q = 1) (hb : d238489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74484, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74484, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74485 q = 1) (hb : d238799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74485, d238799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74485, d238799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73786 (p : Pattern) (ha : d74515 p = 1) (hb : d238810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53562 q = 1) (hb : d238805 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53562, d238805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73751 q ha hb
    | true =>
      simp only [d53562, d238805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73725 q ha hb
  have h3 (q : Pattern) (ha : d53563 q = 1) (hb : d238806 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53563, d238806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53563, d238806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74511 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74512 q = 1) (hb : d238807 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74512, d238807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74512, d238807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74513 q = 1) (hb : d238808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74513, d238808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74513, d238808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74514 q = 1) (hb : d238809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74514, d238809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74514, d238809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74515 q = 1) (hb : d238810 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74515, d238810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74515, d238810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73787 (p : Pattern) (ha : d74521 p = 1) (hb : d238816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74479 q = 1) (hb : d238491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74479, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73783 q ha hb
    | true =>
      simp only [d74479, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73784 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d74480 q = 1) (hb : d238492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74480, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74480, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74481 q = 1) (hb : d238797 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74481, d238797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74481, d238797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74482 q = 1) (hb : d238798 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74482, d238798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74482, d238798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74486 q = 1) (hb : d238800 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74486, d238800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74486, d238800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73785 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74487 q = 1) (hb : d238801 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74487, d238801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74487, d238801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74488 q = 1) (hb : d238802 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74488, d238802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74488, d238802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d74489 q = 1) (hb : d238803 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74489, d238803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74489, d238803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d74490 q = 1) (hb : d238804 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74490, d238804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74490, d238804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74516 q = 1) (hb : d238811 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74516, d238811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d74516, d238811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73786 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74517 q = 1) (hb : d238812 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74517, d238812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74517, d238812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74518 q = 1) (hb : d238813 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74518, d238813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74518, d238813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d74519 q = 1) (hb : d238814 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74519, d238814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74519, d238814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d74520 q = 1) (hb : d238815 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74520, d238815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74520, d238815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d74521 q = 1) (hb : d238816 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74521, d238816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74521, d238816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73788 (p : Pattern) (ha : d74527 p = 1) (hb : d238822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74522 q = 1) (hb : d238817 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74522, d238817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74522, d238817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73787 q ha hb
  have h2 (q : Pattern) (ha : d74523 q = 1) (hb : d238818 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74523, d238818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74523, d238818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74524 q = 1) (hb : d238819 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74524, d238819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74524, d238819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74525 q = 1) (hb : d238820 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74525, d238820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74525, d238820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74526 q = 1) (hb : d238821 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74526, d238821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74526, d238821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74527 q = 1) (hb : d238822 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74527, d238822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74527, d238822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73789 (p : Pattern) (ha : d74533 p = 1) (hb : d238828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74173 q = 1) (hb : d231218 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74173, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59764 q ha hb
    | true =>
      simp only [d74173, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59770 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74258 q = 1) (hb : d231245 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74258, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74258, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59776 q ha hb
  have h3 (q : Pattern) (ha : d74259 q = 1) (hb : d231246 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74259, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74259, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74347 q = 1) (hb : d238764 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74347, d238764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74347, d238764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73776 q ha hb
  have h5 (q : Pattern) (ha : d74348 q = 1) (hb : d238765 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74348, d238765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74348, d238765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74349 q = 1) (hb : d238766 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74349, d238766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74349, d238766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74437 q = 1) (hb : d238793 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74437, d238793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74437, d238793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73782 q ha hb
  have h8 (q : Pattern) (ha : d74438 q = 1) (hb : d238794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74438, d238794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74438, d238794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74439 q = 1) (hb : d238795 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74439, d238795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74439, d238795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74440 q = 1) (hb : d238796 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74440, d238796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74440, d238796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74528 q = 1) (hb : d238823 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74528, d238823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74528, d238823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73788 q ha hb
  have h12 (q : Pattern) (ha : d74529 q = 1) (hb : d238824 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74529, d238824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74529, d238824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74530 q = 1) (hb : d238825 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74530, d238825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74530, d238825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74531 q = 1) (hb : d238826 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74531, d238826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74531, d238826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74532 q = 1) (hb : d238827 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74532, d238827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74532, d238827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74533 q = 1) (hb : d238828 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74533, d238828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74533, d238828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro73790 (p : Pattern) (ha : d74539 p = 1) (hb : d238834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74534 q = 1) (hb : d238829 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74534, d238829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73789 q ha hb
    | true =>
      simp only [d74534, d238829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74535 q = 1) (hb : d238830 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74535, d238830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74535, d238830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74536 q = 1) (hb : d238831 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74536, d238831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74536, d238831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74537 q = 1) (hb : d238832 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74537, d238832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74537, d238832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74538 q = 1) (hb : d238833 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74538, d238833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74538, d238833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74539 q = 1) (hb : d238834 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74539, d238834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74539, d238834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73791 (p : Pattern) (ha : d74545 p = 1) (hb : d238840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74540 q = 1) (hb : d238835 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74540, d238835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73790 q ha hb
    | true =>
      simp only [d74540, d238835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74541 q = 1) (hb : d238836 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74541, d238836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74541, d238836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74542 q = 1) (hb : d238837 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74542, d238837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74542, d238837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74543 q = 1) (hb : d238838 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74543, d238838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74543, d238838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74544 q = 1) (hb : d238839 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74544, d238839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74544, d238839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74545 q = 1) (hb : d238840 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74545, d238840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74545, d238840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73792 (p : Pattern) (ha : d74551 p = 1) (hb : d238846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74546 q = 1) (hb : d238841 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74546, d238841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73791 q ha hb
    | true =>
      simp only [d74546, d238841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74547 q = 1) (hb : d238842 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74547, d238842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74547, d238842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74548 q = 1) (hb : d238843 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74548, d238843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74548, d238843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74549 q = 1) (hb : d238844 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74549, d238844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74549, d238844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74550 q = 1) (hb : d238845 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74550, d238845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74550, d238845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74551 q = 1) (hb : d238846 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74551, d238846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74551, d238846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73793 (p : Pattern) (ha : d74557 p = 1) (hb : d238852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74552 q = 1) (hb : d238847 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74552, d238847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73792 q ha hb
    | true =>
      simp only [d74552, d238847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74553 q = 1) (hb : d238848 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74553, d238848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74553, d238848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74554 q = 1) (hb : d238849 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74554, d238849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74554, d238849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74555 q = 1) (hb : d238850 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74555, d238850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74555, d238850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74556 q = 1) (hb : d238851 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74556, d238851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74556, d238851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74557 q = 1) (hb : d238852 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74557, d238852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74557, d238852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73794 (p : Pattern) (ha : d74563 p = 1) (hb : d238858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74558 q = 1) (hb : d238853 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74558, d238853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73793 q ha hb
    | true =>
      simp only [d74558, d238853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74559 q = 1) (hb : d238854 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74559, d238854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74559, d238854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74560 q = 1) (hb : d238855 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74560, d238855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74560, d238855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74561 q = 1) (hb : d238856 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74561, d238856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74561, d238856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74562 q = 1) (hb : d238857 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74562, d238857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74562, d238857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74563 q = 1) (hb : d238858 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74563, d238858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74563, d238858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73795 (p : Pattern) (ha : d74569 p = 1) (hb : d238864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74564 q = 1) (hb : d238859 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74564, d238859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73794 q ha hb
    | true =>
      simp only [d74564, d238859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74565 q = 1) (hb : d238860 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74565, d238860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74565, d238860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74566 q = 1) (hb : d238861 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74566, d238861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74566, d238861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74567 q = 1) (hb : d238862 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74567, d238862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74567, d238862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74568 q = 1) (hb : d238863 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74568, d238863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74568, d238863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74569 q = 1) (hb : d238864 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74569, d238864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74569, d238864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73796 (p : Pattern) (ha : d74575 p = 1) (hb : d238870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74570 q = 1) (hb : d238865 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74570, d238865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73795 q ha hb
    | true =>
      simp only [d74570, d238865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d74571 q = 1) (hb : d238866 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74571, d238866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74571, d238866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d74572 q = 1) (hb : d238867 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74572, d238867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74572, d238867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d74573 q = 1) (hb : d238868 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74573, d238868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74573, d238868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d74574 q = 1) (hb : d238869 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74574, d238869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74574, d238869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d74575 q = 1) (hb : d238870 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74575, d238870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74575, d238870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro73797 (p : Pattern) (ha : d74690 p = 1) (hb : d238020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4485 q = 1) (hb : d238016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4485, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5560 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d74687 q = 1) (hb : d238017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74687, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74687, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d74688 q = 1) (hb : d238018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74688, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74689 q = 1) (hb : d238019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74689, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74690 q = 1) (hb : d238020 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74690, d238020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74690, d238020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73798 (p : Pattern) (ha : d74694 p = 1) (hb : d238030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d238015 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4485 q = 1) (hb : d238016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4485, d238016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5560 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74687 q = 1) (hb : d238017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74687, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74687, d238017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74688 q = 1) (hb : d238018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74688, d238018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74689 q = 1) (hb : d238019 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74689, d238019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1331 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1336 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d238025 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4490 q = 1) (hb : d238026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4490, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5567 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74691 q = 1) (hb : d238027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74691, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74691, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74692 q = 1) (hb : d238028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74692, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d74692, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74693 q = 1) (hb : d238029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74693, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74693, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d74694 q = 1) (hb : d238030 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74694, d238030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74694, d238030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73799 (p : Pattern) (ha : d74701 p = 1) (hb : d238740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238025 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4490 q = 1) (hb : d238026 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4490, d238026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5567 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74691 q = 1) (hb : d238027 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74691, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74691, d238027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74699 q = 1) (hb : d238028 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74699, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74699, d238028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74700 q = 1) (hb : d238029 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74700, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74700, d238029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74701 q = 1) (hb : d238740 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74701, d238740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74701, d238740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73800 (p : Pattern) (ha : d74710 p = 1) (hb : d238751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238746 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4505 q = 1) (hb : d238747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d238747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4505, d238747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5604 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74707 q = 1) (hb : d238748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74707, d238748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74707, d238748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74708 q = 1) (hb : d238749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74708, d238749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74708, d238749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74709 q = 1) (hb : d238750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74709, d238750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74709, d238750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74710 q = 1) (hb : d238751 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74710, d238751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74710, d238751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73801 (p : Pattern) (ha : d74716 p = 1) (hb : d238757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74695 q = 1) (hb : d238031 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74695, d238031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73797 q ha hb
    | true =>
      simp only [d74695, d238031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73798 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d74696 q = 1) (hb : d238032 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74696, d238032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74696, d238032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74697 q = 1) (hb : d238738 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74697, d238738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74697, d238738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74698 q = 1) (hb : d238739 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74698, d238739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74698, d238739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74702 q = 1) (hb : d238741 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74702, d238741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74702, d238741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73799 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74703 q = 1) (hb : d238742 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74703, d238742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74703, d238742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74704 q = 1) (hb : d238743 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74704, d238743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74704, d238743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74705 q = 1) (hb : d238744 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74705, d238744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74705, d238744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74706 q = 1) (hb : d238745 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74706, d238745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74706, d238745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74711 q = 1) (hb : d238752 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74711, d238752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74711, d238752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73800 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74712 q = 1) (hb : d238753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74712, d238753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74712, d238753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74713 q = 1) (hb : d238754 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74713, d238754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74713, d238754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74714 q = 1) (hb : d238755 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74714, d238755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74714, d238755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74715 q = 1) (hb : d238756 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74715, d238756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74715, d238756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74716 q = 1) (hb : d238757 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74716, d238757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74716, d238757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73802 (p : Pattern) (ha : d74722 p = 1) (hb : d238763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74717 q = 1) (hb : d238758 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74717, d238758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74717, d238758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73801 q ha hb
  have h2 (q : Pattern) (ha : d74718 q = 1) (hb : d238759 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74718, d238759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74718, d238759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74719 q = 1) (hb : d238760 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74719, d238760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74719, d238760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74720 q = 1) (hb : d238761 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74720, d238761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74720, d238761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74721 q = 1) (hb : d238762 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74721, d238762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74721, d238762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74722 q = 1) (hb : d238763 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74722, d238763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74722, d238763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73803 (p : Pattern) (ha : d74729 p = 1) (hb : d238256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4525 q = 1) (hb : d238252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4525, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5650 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d74726 q = 1) (hb : d238253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74726, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74726, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d74727 q = 1) (hb : d238254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74727, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74728 q = 1) (hb : d238255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74728, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74729 q = 1) (hb : d238256 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74729, d238256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74729, d238256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73804 (p : Pattern) (ha : d74733 p = 1) (hb : d238266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d238251 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4525 q = 1) (hb : d238252 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4525, d238252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5650 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74726 q = 1) (hb : d238253 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74726, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74726, d238253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74727 q = 1) (hb : d238254 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74727, d238254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74728 q = 1) (hb : d238255 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74728, d238255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d1813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d238261 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4530 q = 1) (hb : d238262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4530, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5657 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74730 q = 1) (hb : d238263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74730, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74730, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74731 q = 1) (hb : d238264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74731, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d74731, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74732 q = 1) (hb : d238265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74732, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74732, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d74733 q = 1) (hb : d238266 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74733, d238266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74733, d238266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73805 (p : Pattern) (ha : d74740 p = 1) (hb : d238769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238261 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4530 q = 1) (hb : d238262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4530, d238262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5657 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74730 q = 1) (hb : d238263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74730, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74730, d238263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74738 q = 1) (hb : d238264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74738, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74738, d238264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74739 q = 1) (hb : d238265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74739, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74739, d238265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74740 q = 1) (hb : d238769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74740, d238769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74740, d238769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73806 (p : Pattern) (ha : d74749 p = 1) (hb : d238780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1914 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4545 q = 1) (hb : d238776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d238776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4545, d238776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5694 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74746 q = 1) (hb : d238777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74746, d238777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74746, d238777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74747 q = 1) (hb : d238778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74747, d238778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74747, d238778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74748 q = 1) (hb : d238779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74748, d238779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74748, d238779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74749 q = 1) (hb : d238780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74749, d238780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74749, d238780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73807 (p : Pattern) (ha : d74755 p = 1) (hb : d238786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74734 q = 1) (hb : d238267 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74734, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73803 q ha hb
    | true =>
      simp only [d74734, d238267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73804 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d74735 q = 1) (hb : d238268 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74735, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74735, d238268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74736 q = 1) (hb : d238767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74736, d238767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74736, d238767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74737 q = 1) (hb : d238768 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74737, d238768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74737, d238768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74741 q = 1) (hb : d238770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74741, d238770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74741, d238770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73805 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74742 q = 1) (hb : d238771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74742, d238771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74742, d238771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74743 q = 1) (hb : d238772 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74743, d238772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74743, d238772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74744 q = 1) (hb : d238773 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74744, d238773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74744, d238773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74745 q = 1) (hb : d238774 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74745, d238774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74745, d238774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74750 q = 1) (hb : d238781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74750, d238781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74750, d238781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73806 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74751 q = 1) (hb : d238782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74751, d238782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74751, d238782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74752 q = 1) (hb : d238783 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74752, d238783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74752, d238783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74753 q = 1) (hb : d238784 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74753, d238784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74753, d238784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74754 q = 1) (hb : d238785 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74754, d238785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74754, d238785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74755 q = 1) (hb : d238786 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74755, d238786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74755, d238786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73808 (p : Pattern) (ha : d74761 p = 1) (hb : d238792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74756 q = 1) (hb : d238787 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74756, d238787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74756, d238787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73807 q ha hb
  have h2 (q : Pattern) (ha : d74757 q = 1) (hb : d238788 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74757, d238788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74757, d238788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74758 q = 1) (hb : d238789 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74758, d238789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74758, d238789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74759 q = 1) (hb : d238790 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74759, d238790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74759, d238790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74760 q = 1) (hb : d238791 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74760, d238791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74760, d238791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74761 q = 1) (hb : d238792 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74761, d238792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74761, d238792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73809 (p : Pattern) (ha : d74769 p = 1) (hb : d238480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4566 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d4566, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5741 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d74766 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74766, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74766, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d74767 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74767, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d74767, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74768 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74768, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74768, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74769 q = 1) (hb : d238480 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74769, d238480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74769, d238480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73810 (p : Pattern) (ha : d74773 p = 1) (hb : d238490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d238475 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4566 q = 1) (hb : d238476 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d4566, d238476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5741 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74766 q = 1) (hb : d238477 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74766, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74766, d238477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d74767 q = 1) (hb : d238478 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74767, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d74767, d238478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74768 q = 1) (hb : d238479 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74768, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74768, d238479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2286 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d2291 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d238485 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4571 q = 1) (hb : d238486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d4571, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5748 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74770 q = 1) (hb : d238487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74770, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74770, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74771 q = 1) (hb : d238488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74771, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d74771, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74772 q = 1) (hb : d238489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74772, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d74772, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d74773 q = 1) (hb : d238490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74773, d238490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74773, d238490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro73811 (p : Pattern) (ha : d74780 p = 1) (hb : d238799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238485 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4571 q = 1) (hb : d238486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4571, d238486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5748 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74770 q = 1) (hb : d238487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74770, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74770, d238487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74778 q = 1) (hb : d238488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74778, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74778, d238488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74779 q = 1) (hb : d238489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74779, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74779, d238489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74780 q = 1) (hb : d238799 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74780, d238799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74780, d238799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73812 (p : Pattern) (ha : d74789 p = 1) (hb : d238810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d238805 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4586 q = 1) (hb : d238806 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d238806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d4586, d238806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5785 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74786 q = 1) (hb : d238807 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74786, d238807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74786, d238807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d74787 q = 1) (hb : d238808 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74787, d238808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74787, d238808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74788 q = 1) (hb : d238809 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74788, d238809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74788, d238809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74789 q = 1) (hb : d238810 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74789, d238810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74789, d238810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73813 (p : Pattern) (ha : d74795 p = 1) (hb : d238816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74774 q = 1) (hb : d238491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74774, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73809 q ha hb
    | true =>
      simp only [d74774, d238491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73810 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d74775 q = 1) (hb : d238492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74775, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74775, d238492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d74776 q = 1) (hb : d238797 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74776, d238797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74776, d238797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74777 q = 1) (hb : d238798 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74777, d238798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d74777, d238798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74781 q = 1) (hb : d238800 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74781, d238800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74781, d238800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73811 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d74782 q = 1) (hb : d238801 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74782, d238801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74782, d238801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d74783 q = 1) (hb : d238802 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74783, d238802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74783, d238802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d74784 q = 1) (hb : d238803 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74784, d238803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74784, d238803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d74785 q = 1) (hb : d238804 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74785, d238804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74785, d238804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74790 q = 1) (hb : d238811 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74790, d238811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74790, d238811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73812 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d74791 q = 1) (hb : d238812 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74791, d238812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74791, d238812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d74792 q = 1) (hb : d238813 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74792, d238813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74792, d238813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d74793 q = 1) (hb : d238814 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74793, d238814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74793, d238814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d74794 q = 1) (hb : d238815 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74794, d238815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74794, d238815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d74795 q = 1) (hb : d238816 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74795, d238816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d74795, d238816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73814 (p : Pattern) (ha : d74801 p = 1) (hb : d238822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74796 q = 1) (hb : d238817 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74796, d238817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74796, d238817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73813 q ha hb
  have h2 (q : Pattern) (ha : d74797 q = 1) (hb : d238818 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74797, d238818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74797, d238818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74798 q = 1) (hb : d238819 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74798, d238819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74798, d238819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74799 q = 1) (hb : d238820 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74799, d238820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74799, d238820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74800 q = 1) (hb : d238821 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74800, d238821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74800, d238821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74801 q = 1) (hb : d238822 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74801, d238822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74801, d238822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73815 (p : Pattern) (ha : d74807 p = 1) (hb : d238828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d74648 q = 1) (hb : d231218 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74648, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59808 q ha hb
    | true =>
      simp only [d74648, d231218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59814 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74685 q = 1) (hb : d231245 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74685, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74685, d231245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro59820 q ha hb
  have h3 (q : Pattern) (ha : d74686 q = 1) (hb : d231246 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74686, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74686, d231246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74723 q = 1) (hb : d238764 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74723, d238764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74723, d238764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73802 q ha hb
  have h5 (q : Pattern) (ha : d74724 q = 1) (hb : d238765 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74724, d238765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74724, d238765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74725 q = 1) (hb : d238766 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74725, d238766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74725, d238766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74762 q = 1) (hb : d238793 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74762, d238793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74762, d238793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73808 q ha hb
  have h8 (q : Pattern) (ha : d74763 q = 1) (hb : d238794 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74763, d238794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74763, d238794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74764 q = 1) (hb : d238795 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74764, d238795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74764, d238795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74765 q = 1) (hb : d238796 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74765, d238796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74765, d238796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74802 q = 1) (hb : d238823 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74802, d238823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74802, d238823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73814 q ha hb
  have h12 (q : Pattern) (ha : d74803 q = 1) (hb : d238824 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74803, d238824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74803, d238824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74804 q = 1) (hb : d238825 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74804, d238825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74804, d238825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74805 q = 1) (hb : d238826 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74805, d238826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74805, d238826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74806 q = 1) (hb : d238827 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74806, d238827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74806, d238827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74807 q = 1) (hb : d238828 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74807, d238828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74807, d238828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro73816 (p : Pattern) (ha : d74813 p = 1) (hb : d238834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74808 q = 1) (hb : d238829 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74808, d238829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73815 q ha hb
    | true =>
      simp only [d74808, d238829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74809 q = 1) (hb : d238830 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74809, d238830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74809, d238830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74810 q = 1) (hb : d238831 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74810, d238831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74810, d238831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74811 q = 1) (hb : d238832 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74811, d238832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74811, d238832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74812 q = 1) (hb : d238833 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74812, d238833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74812, d238833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74813 q = 1) (hb : d238834 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74813, d238834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74813, d238834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73817 (p : Pattern) (ha : d74819 p = 1) (hb : d238840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74814 q = 1) (hb : d238835 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74814, d238835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73816 q ha hb
    | true =>
      simp only [d74814, d238835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74815 q = 1) (hb : d238836 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74815, d238836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74815, d238836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74816 q = 1) (hb : d238837 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74816, d238837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74816, d238837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74817 q = 1) (hb : d238838 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74817, d238838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74817, d238838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74818 q = 1) (hb : d238839 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74818, d238839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74818, d238839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74819 q = 1) (hb : d238840 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74819, d238840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74819, d238840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73818 (p : Pattern) (ha : d74825 p = 1) (hb : d238846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74820 q = 1) (hb : d238841 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74820, d238841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73817 q ha hb
    | true =>
      simp only [d74820, d238841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74821 q = 1) (hb : d238842 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74821, d238842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74821, d238842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74822 q = 1) (hb : d238843 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74822, d238843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74822, d238843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74823 q = 1) (hb : d238844 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74823, d238844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74823, d238844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74824 q = 1) (hb : d238845 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74824, d238845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74824, d238845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74825 q = 1) (hb : d238846 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74825, d238846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74825, d238846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73819 (p : Pattern) (ha : d74831 p = 1) (hb : d238852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74826 q = 1) (hb : d238847 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, d238847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73818 q ha hb
    | true =>
      simp only [d74826, d238847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74827 q = 1) (hb : d238848 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, d238848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74827, d238848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74828 q = 1) (hb : d238849 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, d238849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74828, d238849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74829 q = 1) (hb : d238850 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d238850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74829, d238850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74830 q = 1) (hb : d238851 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, d238851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74830, d238851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74831 q = 1) (hb : d238852 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d238852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74831, d238852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73820 (p : Pattern) (ha : d74837 p = 1) (hb : d238858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d238853 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, d238853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73819 q ha hb
    | true =>
      simp only [d74832, d238853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d238854 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, d238854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, d238854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d238855 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, d238855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, d238855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d238856 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, d238856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, d238856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d238857 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, d238857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, d238857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d238858 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, d238858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, d238858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73821 (p : Pattern) (ha : d74843 p = 1) (hb : d238864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d238859 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, d238859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73820 q ha hb
    | true =>
      simp only [d74838, d238859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d238860 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, d238860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, d238860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d238861 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, d238861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, d238861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d238862 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, d238862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, d238862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d238863 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, d238863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, d238863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d238864 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, d238864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, d238864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73822 (p : Pattern) (ha : d74849 p = 1) (hb : d238870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d238865 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, d238865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73821 q ha hb
    | true =>
      simp only [d74844, d238865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d238866 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, d238866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, d238866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d238867 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, d238867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, d238867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d238868 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, d238868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, d238868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d238869 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, d238869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, d238869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d238870 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, d238870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, d238870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73823 (p : Pattern) (ha : d132 p = 1) (hb : d253269 p = 1) : d40151 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15 q = 1) (hb : d253269 q = 1) : d15 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d130 q = 1) (hb : d253269 q = 1) : d40149 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16 q = 1) (hb : d253269 q = 1) : d16 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d131 q = 1) (hb : d253269 q = 1) : d40150 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d40150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131, d40150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17 q = 1) (hb : d253269 q = 1) : d17 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d132 q = 1) (hb : d253269 q = 1) : d40151 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d132, d40151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d132, d40151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73824 (p : Pattern) (ha : d138 p = 1) (hb : d287734 p = 1) : d40157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d287734 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d287734 q = 1) : d40154 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d287734 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d287734 q = 1) : d40155 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d40155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136, d40155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137 q = 1) (hb : d287734 q = 1) : d40156 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d40156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d40156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d23 q = 1) (hb : d287734 q = 1) : d23 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d138 q = 1) (hb : d287734 q = 1) : d40157 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d40157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d138, d40157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73825 (p : Pattern) (ha : d144 p = 1) (hb : d287734 p = 1) : d40163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d287734 q = 1) : d40158 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73824 q ha hb
    | true =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d287734 q = 1) : d40159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d287734 q = 1) : d40160 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d40160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d40160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d287734 q = 1) : d40161 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d40161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d40161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d287734 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d287734 q = 1) : d40162 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d40162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d40162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d287734 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d287734 q = 1) : d40163 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d40163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d40163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73826 (p : Pattern) (ha : d150 p = 1) (hb : d287734 p = 1) : d40169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d287734 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d287734 q = 1) : d40164 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73825 q ha hb
    | true =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d287734 q = 1) : d40165 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d287734 q = 1) : d40166 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d287734 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d287734 q = 1) : d40167 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d40167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d40167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d287734 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d287734 q = 1) : d40168 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d40168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d40168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d287734 q = 1) : d40169 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d40169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d40169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro73827 (p : Pattern) (ha : d203 p = 1) (hb : d287734 p = 1) : d40182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d287734 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73826 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d287734 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287734 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d287734 q = 1) : d40172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d287734 q = 1) : d40173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d287734 q = 1) : d40174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d40174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d40174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d287734 q = 1) : d40182 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d40182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d40182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro73828 (p : Pattern) (ha : d4349 p = 1) (hb : d287734 p = 1) : d289294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d287734 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d287734 q = 1) : d40183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73827 q ha hb
    | true =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d287734 q = 1) : d289283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d287734 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d287734 q = 1) : d289284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d287734 q = 1) : d289292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d289292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d289292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d287734 q = 1) : d289293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d289293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d289293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d287734 q = 1) : d289294 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d289294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d289294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73829 (p : Pattern) (ha : d231 p = 1) (hb : d287734 p = 1) : d40206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d287734 q = 1) : d40201 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d40201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d40201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73824 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d287734 q = 1) : d40158 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73824 q ha hb
    | true =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d287734 q = 1) : d40202 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d40202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d40202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d287734 q = 1) : d40159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d287734 q = 1) : d40203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d40203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d40203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d287734 q = 1) : d40204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d40204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d40204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d287734 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d287734 q = 1) : d40205 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d40205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d40205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d287734 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d287734 q = 1) : d40206 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d40206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d40206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73830 (p : Pattern) (ha : d237 p = 1) (hb : d287734 p = 1) : d40212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d287734 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d287734 q = 1) : d40207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73829 q ha hb
    | true =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d287734 q = 1) : d40208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d287734 q = 1) : d40209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d287734 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d287734 q = 1) : d40210 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d40210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d40210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d287734 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d287734 q = 1) : d40211 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d40211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d40211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d287734 q = 1) : d40212 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d40212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d40212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro73831 (p : Pattern) (ha : d243 p = 1) (hb : d287734 p = 1) : d40218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d287734 q = 1) : d40213 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d40213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73830 q ha hb
    | true =>
      simp only [d238, d40213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d287734 q = 1) : d40214 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d40214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d40214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d287734 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d287734 q = 1) : d40215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d40215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d40215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d287734 q = 1) : d40216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d40216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d40216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d287734 q = 1) : d40217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d40217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d40217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d287734 q = 1) : d40218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d40218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d40218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro73832 (p : Pattern) (ha : d4359 p = 1) (hb : d287734 p = 1) : d289304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d287734 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d287734 q = 1) : d40219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d40219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73831 q ha hb
    | true =>
      simp only [d244, d40219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d287734 q = 1) : d289300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d289300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d289300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d287734 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d287734 q = 1) : d289301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d289301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d289301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d287734 q = 1) : d289302 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d289302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d289302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d287734 q = 1) : d289303 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d289303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d289303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d287734 q = 1) : d289304 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d289304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d289304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73833 (p : Pattern) (ha : d156 p = 1) (hb : d287734 p = 1) : d40175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d287734 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73826 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d287734 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287734 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d287734 q = 1) : d40172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d287734 q = 1) : d40173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d287734 q = 1) : d40174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d40174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d40174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d287734 q = 1) : d40175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d40175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d40175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro73834 (p : Pattern) (ha : d51643 p = 1) (hb : d287734 p = 1) : d289282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d287734 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d287734 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d287734 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d287734 q = 1) : d40176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73833 q ha hb
    | true =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d287734 q = 1) : d289278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d287734 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d287734 q = 1) : d289279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d287734 q = 1) : d289280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d287734 q = 1) : d289281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d287734 q = 1) : d289282 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d289282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d289282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73835 (p : Pattern) (ha : d51646 p = 1) (hb : d287734 p = 1) : d289287 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d287734 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d287734 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d287734 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d287734 q = 1) : d40176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73833 q ha hb
    | true =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d287734 q = 1) : d289278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d289278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d287734 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d287734 q = 1) : d289279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d289279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d287734 q = 1) : d289280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d289280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d287734 q = 1) : d289281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d289281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d287734 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d287734 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d287734 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d287734 q = 1) : d40183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73827 q ha hb
    | true =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d287734 q = 1) : d289283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d289283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d287734 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d287734 q = 1) : d289284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d289284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d287734 q = 1) : d289285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d289285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d289285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d287734 q = 1) : d289286 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d289286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d289286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d287734 q = 1) : d289287 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d289287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d289287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73836 (p : Pattern) (ha : d51652 p = 1) (hb : d287734 p = 1) : d289310 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d287734 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d287734 q = 1) : d289288 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d289288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73834 q ha hb
    | true =>
      simp only [d51647, d289288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73835 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d287734 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d287734 q = 1) : d289289 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d289289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d289289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d287734 q = 1) : d289290 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d289290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d289290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d287734 q = 1) : d289291 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d289291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d289291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d287734 q = 1) : d289295 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d289295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d289295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73828 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d287734 q = 1) : d289296 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d289296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d289296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d287734 q = 1) : d289297 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d289297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d289297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d287734 q = 1) : d289298 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d289298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d289298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d287734 q = 1) : d289299 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d289299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d289299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d287734 q = 1) : d289305 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d289305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d289305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73832 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d287734 q = 1) : d289306 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d289306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d289306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d287734 q = 1) : d289307 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d289307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d289307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d287734 q = 1) : d289308 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d289308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d289308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d287734 q = 1) : d289309 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d289309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d289309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d287734 q = 1) : d289310 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d289310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d289310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro73837 (p : Pattern) (ha : d284 p = 1) (hb : d287734 p = 1) : d40240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d287734 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d287734 q = 1) : d40176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73833 q ha hb
    | true =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d287734 q = 1) : d40236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d287734 q = 1) : d40237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d287734 q = 1) : d40238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d287734 q = 1) : d40239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d287734 q = 1) : d40240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d40240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d40240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro73838 (p : Pattern) (ha : d291 p = 1) (hb : d287734 p = 1) : d40247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d287734 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d287734 q = 1) : d40176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73833 q ha hb
    | true =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d287734 q = 1) : d40236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d287734 q = 1) : d40237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d287734 q = 1) : d40238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d287734 q = 1) : d40239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d287734 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d287734 q = 1) : d40183 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73827 q ha hb
    | true =>
      simp only [d204, d40183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d287734 q = 1) : d40243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d40243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d40243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d287734 q = 1) : d40244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d40244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d40244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d287734 q = 1) : d40245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d40245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d40245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d287734 q = 1) : d40246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d40246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d40246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d287734 q = 1) : d40247 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d40247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d40247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro73839 (p : Pattern) (ha : d397 p = 1) (hb : d287734 p = 1) : d40359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d287734 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d287734 q = 1) : d40176 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73833 q ha hb
    | true =>
      simp only [d157, d40176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d287734 q = 1) : d40236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d40236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d287734 q = 1) : d40237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d40237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d287734 q = 1) : d40238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d40238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d287734 q = 1) : d40239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d40239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d287734 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d287734 q = 1) : d40359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d40359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d40359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73840 (p : Pattern) (ha : d296 p = 1) (hb : d287734 p = 1) : d40252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d287734 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73826 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d287734 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287734 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d287734 q = 1) : d40172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d287734 q = 1) : d40173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d287734 q = 1) : d40251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d40251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d40251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d287734 q = 1) : d40252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d40252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d40252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro73841 (p : Pattern) (ha : d303 p = 1) (hb : d287734 p = 1) : d40259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d287734 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73826 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d287734 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287734 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d287734 q = 1) : d40172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d287734 q = 1) : d40257 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d40257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d40257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d287734 q = 1) : d40258 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d40258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d40258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d287734 q = 1) : d40259 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d40259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d40259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro73842 (p : Pattern) (ha : d4736 p = 1) (hb : d287734 p = 1) : d40330 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d287734 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73826 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d287734 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d287734 q = 1) : d40327 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d40327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d40327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d287734 q = 1) : d40328 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d40328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d40328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d287734 q = 1) : d40329 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d40329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d40329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d287734 q = 1) : d40330 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d40330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d40330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73843 (p : Pattern) (ha : d312 p = 1) (hb : d253269 p = 1) : d40264 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d310 q = 1) (hb : d253269 q = 1) : d2017 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15 q = 1) (hb : d253269 q = 1) : d15 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d130 q = 1) (hb : d253269 q = 1) : d40149 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d311 q = 1) (hb : d253269 q = 1) : d40263 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d40263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d311, d40263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16 q = 1) (hb : d253269 q = 1) : d16 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d131 q = 1) (hb : d253269 q = 1) : d40150 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d40150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d131, d40150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d312 q = 1) (hb : d253269 q = 1) : d40264 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d312, d40264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d312, d40264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro73844 (p : Pattern) (ha : d318 p = 1) (hb : d287734 p = 1) : d40270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d287734 q = 1) : d40267 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d287734 q = 1) : d20 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d287734 q = 1) : d40154 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d287734 q = 1) : d40268 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d40268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d40268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d317 q = 1) (hb : d287734 q = 1) : d40269 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d40269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d40269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d21 q = 1) (hb : d287734 q = 1) : d21 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d136 q = 1) (hb : d287734 q = 1) : d40155 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d40155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136, d40155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d137 q = 1) (hb : d287734 q = 1) : d40156 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d40156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d137, d40156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d318 q = 1) (hb : d287734 q = 1) : d40270 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d40270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d318, d40270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro73845 (p : Pattern) (ha : d9381 p = 1) (hb : d287734 p = 1) : d40278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d287734 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d287734 q = 1) : d40154 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5448 q = 1) (hb : d287734 q = 1) : d40276 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d40276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5448, d40276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d5449 q = 1) (hb : d287734 q = 1) : d40277 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d40277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5449, d40277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d287734 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9381 q = 1) (hb : d287734 q = 1) : d40278 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d40278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9381, d40278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro73846 (p : Pattern) (ha : d15966 p = 1) (hb : d287734 p = 1) : d40284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d287734 q = 1) : d40271 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d40271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73844 q ha hb
    | true =>
      simp only [d319, d40271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d287734 q = 1) : d40272 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d40272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d40272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d287734 q = 1) : d40273 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d40273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d40273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d287734 q = 1) : d40274 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d40274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d40274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d287734 q = 1) : d40158 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73824 q ha hb
    | true =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d287734 q = 1) : d40159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d287734 q = 1) : d40160 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d40160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d40160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d287734 q = 1) : d40161 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d40161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d40161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d287734 q = 1) : d40275 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d40275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d40275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d287734 q = 1) : d40279 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73845 q ha hb
    | true =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d287734 q = 1) : d40280 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d287734 q = 1) : d40281 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d40281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d40281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d287734 q = 1) : d40282 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d40282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d40282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d287734 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12495 q = 1) (hb : d287734 q = 1) : d40283 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d40283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12495, d40283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15966 q = 1) (hb : d287734 q = 1) : d40284 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d40284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15966, d40284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro73847 (p : Pattern) (ha : d15972 p = 1) (hb : d287734 p = 1) : d40290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d287734 q = 1) : d40285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d40285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73846 q ha hb
    | true =>
      simp only [d15967, d40285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73825 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d287734 q = 1) : d40286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d40286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d40286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d287734 q = 1) : d40287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d40287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d40287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d287734 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d287734 q = 1) : d40164 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73825 q ha hb
    | true =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d287734 q = 1) : d40165 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d287734 q = 1) : d40166 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d287734 q = 1) : d40288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d40288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d40288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d287734 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d287734 q = 1) : d40167 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d40167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d40167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d287734 q = 1) : d40289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d40289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d40289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d287734 q = 1) : d40290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d40290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d40290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro73848 (p : Pattern) (ha : d15978 p = 1) (hb : d287734 p = 1) : d40296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d287734 q = 1) : d40291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d40291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73847 q ha hb
    | true =>
      simp only [d15973, d40291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d287734 q = 1) : d40292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d40292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d40292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d287734 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73826 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d287734 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d287734 q = 1) : d40293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d40293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d40293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d287734 q = 1) : d40294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d40294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d40294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d287734 q = 1) : d40295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d40295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d40295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d287734 q = 1) : d40296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d40296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d40296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73849 (p : Pattern) (ha : d128195 p = 1) (hb : d287734 p = 1) : d289320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d287734 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d287734 q = 1) : d40253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d40253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73840 q ha hb
    | true =>
      simp only [d297, d40253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d287734 q = 1) : d40254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d40254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d40254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d287734 q = 1) : d40255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d40255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d40255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d287734 q = 1) : d40256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d40256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d40256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d287734 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d287734 q = 1) : d40260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d40260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73841 q ha hb
    | true =>
      simp only [d304, d40260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d287734 q = 1) : d40261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d40261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d40261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d287734 q = 1) : d40262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d40262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d40262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d287734 q = 1) : d40297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d40297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73848 q ha hb
    | true =>
      simp only [d15979, d40297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73833 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d287734 q = 1) : d289316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d289316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d289316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d287734 q = 1) : d40331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d40331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73842 q ha hb
    | true =>
      simp only [d4737, d40331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d287734 q = 1) : d40332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d40332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d40332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d287734 q = 1) : d289317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d289317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d289317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d287734 q = 1) : d289318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d289318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d289318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d287734 q = 1) : d289319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d289319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d289319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128195 q = 1) (hb : d287734 q = 1) : d289320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d289320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d289320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro73850 (p : Pattern) (ha : d376 p = 1) (hb : d287734 p = 1) : d40337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d287734 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73826 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d287734 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287734 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d287734 q = 1) : d40172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d287734 q = 1) : d40173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d40173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d287734 q = 1) : d40251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d40251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d40251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d287734 q = 1) : d40337 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d40337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d40337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro73851 (p : Pattern) (ha : d381 p = 1) (hb : d287734 p = 1) : d40342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d287734 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73826 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d287734 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d287734 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d287734 q = 1) : d40172 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d40172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d287734 q = 1) : d40257 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d40257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d40257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d287734 q = 1) : d40258 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d40258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d40258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d287734 q = 1) : d40342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d40342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d40342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro73852 (p : Pattern) (ha : d5355 p = 1) (hb : d287734 p = 1) : d40351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d287734 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73826 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d287734 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d287734 q = 1) : d40327 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d40327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d40327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d287734 q = 1) : d40328 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d40328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d40328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d287734 q = 1) : d40329 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d40329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d40329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d287734 q = 1) : d40351 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d40351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d40351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73853 (p : Pattern) (ha : d15985 p = 1) (hb : d287734 p = 1) : d40346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d287734 q = 1) : d40291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d40291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73847 q ha hb
    | true =>
      simp only [d15973, d40291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d287734 q = 1) : d40292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d40292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d40292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d287734 q = 1) : d40170 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73826 q ha hb
    | true =>
      simp only [d151, d40170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d287734 q = 1) : d40171 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d40171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d287734 q = 1) : d40293 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d40293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d40293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d287734 q = 1) : d40294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d40294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d40294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d287734 q = 1) : d40295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d40295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d40295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d287734 q = 1) : d40346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d40346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d40346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73854 (p : Pattern) (ha : d128200 p = 1) (hb : d287734 p = 1) : d289325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d287734 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d287734 q = 1) : d40253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d40253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73840 q ha hb
    | true =>
      simp only [d297, d40253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d287734 q = 1) : d40254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d40254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d40254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d287734 q = 1) : d40255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d40255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d40255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d287734 q = 1) : d40256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d40256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d40256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d287734 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d287734 q = 1) : d40260 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d40260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73841 q ha hb
    | true =>
      simp only [d304, d40260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d287734 q = 1) : d40261 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d40261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d40261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d287734 q = 1) : d40262 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d40262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d40262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d287734 q = 1) : d40297 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d40297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73848 q ha hb
    | true =>
      simp only [d15979, d40297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73833 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d287734 q = 1) : d289316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d289316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d289316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d287734 q = 1) : d40331 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d40331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73842 q ha hb
    | true =>
      simp only [d4737, d40331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d287734 q = 1) : d40332 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d40332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d40332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d287734 q = 1) : d289317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d289317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d289317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d287734 q = 1) : d289318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d289318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d289318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d287734 q = 1) : d289319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d289319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d289319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d287734 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d287734 q = 1) : d40338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d40338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73850 q ha hb
    | true =>
      simp only [d377, d40338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d287734 q = 1) : d40339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d40339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d40339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d287734 q = 1) : d40340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d40340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d40340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d287734 q = 1) : d40341 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d40341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d40341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d287734 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d287734 q = 1) : d40343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d40343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73851 q ha hb
    | true =>
      simp only [d382, d40343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d287734 q = 1) : d40344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d40344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d40344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d287734 q = 1) : d40345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d40345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d40345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d15986 q = 1) (hb : d287734 q = 1) : d40347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d40347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73853 q ha hb
    | true =>
      simp only [d15986, d40347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73827 q ha hb
  have h27 (q : Pattern) (ha : d128196 q = 1) (hb : d287734 q = 1) : d289321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d289321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d128196, d289321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d287734 q = 1) : d40352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d40352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73852 q ha hb
    | true =>
      simp only [d5356, d40352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d287734 q = 1) : d40353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d40353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d40353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d128197 q = 1) (hb : d287734 q = 1) : d289322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d289322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d128197, d289322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d128198 q = 1) (hb : d287734 q = 1) : d289323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d289323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d128198, d289323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d128199 q = 1) (hb : d287734 q = 1) : d289324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d289324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128199, d289324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d128200 q = 1) (hb : d287734 q = 1) : d289325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d289325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128200, d289325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro73855 (p : Pattern) (ha : d128207 p = 1) (hb : d287734 p = 1) : d289332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d287734 q = 1) : d40347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d40347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73853 q ha hb
    | true =>
      simp only [d15986, d40347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73827 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d287734 q = 1) : d289321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d289321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d289321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d287734 q = 1) : d40352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d40352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73852 q ha hb
    | true =>
      simp only [d5356, d40352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d287734 q = 1) : d40353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d40353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d40353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d287734 q = 1) : d289322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d289322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d289322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d287734 q = 1) : d289330 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d289330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d289330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d287734 q = 1) : d289331 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d289331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d289331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d287734 q = 1) : d289332 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d289332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d289332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73856 (p : Pattern) (ha : d5377 p = 1) (hb : d287734 p = 1) : d40419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d287734 q = 1) : d40213 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d40213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73830 q ha hb
    | true =>
      simp only [d238, d40213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d287734 q = 1) : d40214 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d40214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d40214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d287734 q = 1) : d40416 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d40416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d40416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d287734 q = 1) : d40417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d40417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d40417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d287734 q = 1) : d40418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d40418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d40418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d287734 q = 1) : d40419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d40419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d40419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73857 (p : Pattern) (ha : d16004 p = 1) (hb : d287734 p = 1) : d40382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d287734 q = 1) : d40372 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d40372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d40372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73844 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d287734 q = 1) : d40271 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d40271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73844 q ha hb
    | true =>
      simp only [d319, d40271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d287734 q = 1) : d40373 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d40373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d40373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d287734 q = 1) : d40272 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d40272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d40272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d287734 q = 1) : d40374 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d40374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d40374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d287734 q = 1) : d40375 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d40375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d40375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d287734 q = 1) : d40201 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d40201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d40201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73824 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d287734 q = 1) : d40158 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73824 q ha hb
    | true =>
      simp only [d139, d40158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d287734 q = 1) : d40202 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d40202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d40202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d287734 q = 1) : d40159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d40159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d287734 q = 1) : d40203 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d40203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d40203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d287734 q = 1) : d40204 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d40204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d40204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d287734 q = 1) : d40376 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d40376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d40376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d287734 q = 1) : d40377 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d40377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d40377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73845 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d287734 q = 1) : d40279 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73845 q ha hb
    | true =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d287734 q = 1) : d40378 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d40378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d40378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d287734 q = 1) : d40280 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12601 q = 1) (hb : d287734 q = 1) : d40379 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d40379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12601, d40379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12602 q = 1) (hb : d287734 q = 1) : d40380 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d40380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12602, d40380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d287734 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d12603 q = 1) (hb : d287734 q = 1) : d40381 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d40381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12603, d40381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d16004 q = 1) (hb : d287734 q = 1) : d40382 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d40382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16004, d40382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro73858 (p : Pattern) (ha : d16010 p = 1) (hb : d287734 p = 1) : d40388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d287734 q = 1) : d40383 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d40383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73857 q ha hb
    | true =>
      simp only [d16005, d40383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73829 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d287734 q = 1) : d40384 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d40384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d40384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d287734 q = 1) : d40385 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d40385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d40385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d287734 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d287734 q = 1) : d40207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73829 q ha hb
    | true =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d287734 q = 1) : d40208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d287734 q = 1) : d40209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d287734 q = 1) : d40386 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d40386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d40386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d287734 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d287734 q = 1) : d40210 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d40210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d40210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16009 q = 1) (hb : d287734 q = 1) : d40387 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d40387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, d40387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16010 q = 1) (hb : d287734 q = 1) : d40388 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d40388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16010, d40388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro73859 (p : Pattern) (ha : d16016 p = 1) (hb : d287734 p = 1) : d40394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d287734 q = 1) : d40389 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d40389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73858 q ha hb
    | true =>
      simp only [d16011, d40389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d287734 q = 1) : d40390 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d40390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d40390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d287734 q = 1) : d40213 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d40213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73830 q ha hb
    | true =>
      simp only [d238, d40213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d287734 q = 1) : d40214 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d40214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d40214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d287734 q = 1) : d40391 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d40391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d40391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d287734 q = 1) : d40392 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d40392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d40392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d287734 q = 1) : d40393 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d40393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d40393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d287734 q = 1) : d40394 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d40394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d40394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73860 (p : Pattern) (ha : d128217 p = 1) (hb : d287734 p = 1) : d289342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d287734 q = 1) : d40395 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d40395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73859 q ha hb
    | true =>
      simp only [d16017, d40395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73831 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d287734 q = 1) : d289338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d289338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d289338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d287734 q = 1) : d40420 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d40420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73856 q ha hb
    | true =>
      simp only [d5378, d40420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d287734 q = 1) : d40421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d40421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d40421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d287734 q = 1) : d289339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d289339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d289339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d287734 q = 1) : d289340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d289340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d289340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d287734 q = 1) : d289341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d289341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d289341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d287734 q = 1) : d289342 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d289342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d289342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73861 (p : Pattern) (ha : d128223 p = 1) (hb : d287734 p = 1) : d289348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d287734 q = 1) : d40241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d40241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d40241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73837 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d287734 q = 1) : d40242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d40242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d40242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d287734 q = 1) : d40248 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d40248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73837 q ha hb
    | true =>
      simp only [d292, d40248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73838 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d287734 q = 1) : d40249 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d40249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d40249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d287734 q = 1) : d40250 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d40250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d40250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d287734 q = 1) : d289326 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d289326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73849 q ha hb
    | true =>
      simp only [d128201, d289326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73854 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d287734 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d287734 q = 1) : d40360 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d40360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73839 q ha hb
    | true =>
      simp only [d398, d40360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128202 q = 1) (hb : d287734 q = 1) : d289327 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d289327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d289327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128203 q = 1) (hb : d287734 q = 1) : d289328 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d289328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128203, d289328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d128204 q = 1) (hb : d287734 q = 1) : d289329 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d289329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d289329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128208 q = 1) (hb : d287734 q = 1) : d289333 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d289333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d289333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73855 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d287734 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d128209 q = 1) (hb : d287734 q = 1) : d289334 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d289334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128209, d289334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128210 q = 1) (hb : d287734 q = 1) : d289335 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d289335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128210, d289335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128211 q = 1) (hb : d287734 q = 1) : d289336 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d289336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128211, d289336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d128212 q = 1) (hb : d287734 q = 1) : d289337 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d289337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128212, d289337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128218 q = 1) (hb : d287734 q = 1) : d289343 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d289343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d289343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73860 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d287734 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d128219 q = 1) (hb : d287734 q = 1) : d289344 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d289344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128219, d289344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d128220 q = 1) (hb : d287734 q = 1) : d289345 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d289345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128220, d289345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128221 q = 1) (hb : d287734 q = 1) : d289346 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d289346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128221, d289346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128222 q = 1) (hb : d287734 q = 1) : d289347 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d289347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128222, d289347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d128223 q = 1) (hb : d287734 q = 1) : d289348 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d289348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128223, d289348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro73862 (p : Pattern) (ha : d128229 p = 1) (hb : d287734 p = 1) : d289354 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d287734 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d287734 q = 1) : d289311 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d289311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d289311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73836 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d287734 q = 1) : d289312 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d289312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d289312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d287734 q = 1) : d289313 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d289313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d289313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d287734 q = 1) : d289314 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d289314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d289314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d287734 q = 1) : d289315 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d289315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d289315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d287734 q = 1) : d289349 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d289349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d289349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73861 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d287734 q = 1) : d289350 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d289350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d289350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d287734 q = 1) : d289351 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d289351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d289351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d287734 q = 1) : d289352 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d289352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d289352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d287734 q = 1) : d289353 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d289353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d289353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d287734 q = 1) : d289354 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d289354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d289354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro73863 (p : Pattern) (ha : d481 p = 1) (hb : d287734 p = 1) : d40444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d287734 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d287734 q = 1) : d40164 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73825 q ha hb
    | true =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d287734 q = 1) : d40165 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d287734 q = 1) : d40166 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d287734 q = 1) : d40438 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d40438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d40438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d287734 q = 1) : d40443 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d40443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d40443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d287734 q = 1) : d40444 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d40444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d40444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro73864 (p : Pattern) (ha : d491 p = 1) (hb : d287734 p = 1) : d40454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d287734 q = 1) : d40451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d287734 q = 1) : d40452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d40452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d40452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d287734 q = 1) : d40453 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d40453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d40453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d287734 q = 1) : d40454 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d40454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d40454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73865 (p : Pattern) (ha : d501 p = 1) (hb : d287734 p = 1) : d40464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d287734 q = 1) : d40451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d287734 q = 1) : d40452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d40452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d40452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d287734 q = 1) : d40453 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d40453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d40453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d287734 q = 1) : d40464 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d40464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d40464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73866 (p : Pattern) (ha : d644 p = 1) (hb : d287734 p = 1) : d40631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d287734 q = 1) : d40620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d40620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73864 q ha hb
    | true =>
      simp only [d633, d40620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d287734 q = 1) : d40621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d40621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d40621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d287734 q = 1) : d40622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d40622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d40622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d287734 q = 1) : d40623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d40623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d40623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d287734 q = 1) : d40624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d40624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d40624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d287734 q = 1) : d40626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d40626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73865 q ha hb
    | true =>
      simp only [d639, d40626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d287734 q = 1) : d40627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d40627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d40627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d287734 q = 1) : d40628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d40628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d40628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d287734 q = 1) : d40629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d40629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d40629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d287734 q = 1) : d40630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d40630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d40630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d287734 q = 1) : d40631 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d40631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d40631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73867 (p : Pattern) (ha : d653 p = 1) (hb : d287734 p = 1) : d40640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d287734 q = 1) : d40626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d40626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73865 q ha hb
    | true =>
      simp only [d639, d40626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d287734 q = 1) : d40627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d40627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d40627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d287734 q = 1) : d40628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d40628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d40628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d287734 q = 1) : d40629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d40629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d40629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d287734 q = 1) : d40630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d40630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d40630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d287734 q = 1) : d40640 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d40640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d40640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73868 (p : Pattern) (ha : d683 p = 1) (hb : d287734 p = 1) : d40683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d287734 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d287734 q = 1) : d40207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73829 q ha hb
    | true =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d287734 q = 1) : d40208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d287734 q = 1) : d40209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d287734 q = 1) : d40673 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d40673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d40673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d287734 q = 1) : d40682 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d40682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d40682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d287734 q = 1) : d40683 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d40683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d40683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro73869 (p : Pattern) (ha : d730 p = 1) (hb : d287734 p = 1) : d40739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d287734 q = 1) : d40684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d40684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73868 q ha hb
    | true =>
      simp only [d684, d40684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d287734 q = 1) : d40685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d40685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d40685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d287734 q = 1) : d40736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d40736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d40736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d287734 q = 1) : d40737 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d40737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d40737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d287734 q = 1) : d40738 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d40738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d40738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d287734 q = 1) : d40739 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d40739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d40739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73870 (p : Pattern) (ha : d736 p = 1) (hb : d287734 p = 1) : d40745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d287734 q = 1) : d40740 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d40740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73869 q ha hb
    | true =>
      simp only [d731, d40740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d287734 q = 1) : d40741 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d40741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d40741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d287734 q = 1) : d40742 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d40742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d40742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d287734 q = 1) : d40743 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d40743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d40743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d287734 q = 1) : d40744 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d40744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d40744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d287734 q = 1) : d40745 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d40745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d40745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73871 (p : Pattern) (ha : d16036 p = 1) (hb : d287734 p = 1) : d40440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d287734 q = 1) : d40285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d40285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73846 q ha hb
    | true =>
      simp only [d15967, d40285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73825 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d287734 q = 1) : d40286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d40286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d40286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d287734 q = 1) : d40287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d40287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d40287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d287734 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d287734 q = 1) : d40164 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73825 q ha hb
    | true =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d287734 q = 1) : d40165 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d287734 q = 1) : d40166 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d287734 q = 1) : d40288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d40288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d40288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d287734 q = 1) : d40438 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d40438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d40438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16035 q = 1) (hb : d287734 q = 1) : d40439 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d40439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16035, d40439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16036 q = 1) (hb : d287734 q = 1) : d40440 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d40440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16036, d40440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro73872 (p : Pattern) (ha : d16042 p = 1) (hb : d287734 p = 1) : d40450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d287734 q = 1) : d40441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73871 q ha hb
    | true =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d287734 q = 1) : d40442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d287734 q = 1) : d40447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d287734 q = 1) : d40448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d40448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d40448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d287734 q = 1) : d40449 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d40449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d40449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d287734 q = 1) : d40450 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d40450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d40450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73873 (p : Pattern) (ha : d16048 p = 1) (hb : d287734 p = 1) : d40460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d287734 q = 1) : d40455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d40455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73872 q ha hb
    | true =>
      simp only [d16043, d40455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73864 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d287734 q = 1) : d40456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d40456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d40456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d287734 q = 1) : d40457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d40457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d40457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d287734 q = 1) : d40458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d40458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d40458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d287734 q = 1) : d40459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d40459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d40459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d287734 q = 1) : d40460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d40460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d40460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73874 (p : Pattern) (ha : d16051 p = 1) (hb : d287734 p = 1) : d40463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d287734 q = 1) : d40441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73871 q ha hb
    | true =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d287734 q = 1) : d40442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d287734 q = 1) : d40447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d287734 q = 1) : d40448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d40448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d40448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d287734 q = 1) : d40449 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d40449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d40449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d287734 q = 1) : d40463 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d40463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d40463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73875 (p : Pattern) (ha : d16057 p = 1) (hb : d287734 p = 1) : d40470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d287734 q = 1) : d40455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d40455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73872 q ha hb
    | true =>
      simp only [d16043, d40455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73864 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d287734 q = 1) : d40456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d40456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d40456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d287734 q = 1) : d40457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d40457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d40457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d287734 q = 1) : d40458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d40458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d40458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d287734 q = 1) : d40459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d40459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d40459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d287734 q = 1) : d40465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d40465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73874 q ha hb
    | true =>
      simp only [d16052, d40465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73865 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d287734 q = 1) : d40466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d40466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d40466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d287734 q = 1) : d40467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d40467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d40467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d287734 q = 1) : d40468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d40468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d40468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d287734 q = 1) : d40469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d40469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d40469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d287734 q = 1) : d40470 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d40470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d40470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73876 (p : Pattern) (ha : d16143 p = 1) (hb : d287734 p = 1) : d40625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d287734 q = 1) : d40455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d40455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73872 q ha hb
    | true =>
      simp only [d16043, d40455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73864 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d287734 q = 1) : d40456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d40456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d40456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d287734 q = 1) : d40457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d40457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d40457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d287734 q = 1) : d40458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d40458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d40458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d287734 q = 1) : d40459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d40459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d40459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d287734 q = 1) : d40620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d40620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73864 q ha hb
    | true =>
      simp only [d633, d40620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d287734 q = 1) : d40621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d40621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d40621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d287734 q = 1) : d40622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d40622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d40622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d287734 q = 1) : d40623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d40623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d40623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d287734 q = 1) : d40624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d40624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d40624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d287734 q = 1) : d40625 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d40625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d40625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73877 (p : Pattern) (ha : d514 p = 1) (hb : d287734 p = 1) : d40477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d287734 q = 1) : d40451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d287734 q = 1) : d40452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d40452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d40452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d287734 q = 1) : d40476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d40476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d40476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d287734 q = 1) : d40477 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d40477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d40477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73878 (p : Pattern) (ha : d524 p = 1) (hb : d287734 p = 1) : d40487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d287734 q = 1) : d40451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d287734 q = 1) : d40485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d40485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d40485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d287734 q = 1) : d40486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d40486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d40486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d287734 q = 1) : d40487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d40487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d40487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73879 (p : Pattern) (ha : d16062 p = 1) (hb : d287734 p = 1) : d40475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d287734 q = 1) : d40441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73871 q ha hb
    | true =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d287734 q = 1) : d40442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d287734 q = 1) : d40447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d287734 q = 1) : d40448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d40448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d40448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d287734 q = 1) : d40474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d40474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d40474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d287734 q = 1) : d40475 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d40475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d40475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73880 (p : Pattern) (ha : d16069 p = 1) (hb : d287734 p = 1) : d40484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d287734 q = 1) : d40441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73871 q ha hb
    | true =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d287734 q = 1) : d40442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d287734 q = 1) : d40447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d287734 q = 1) : d40482 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d40482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d40482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d287734 q = 1) : d40483 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d40483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d40483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d287734 q = 1) : d40484 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d40484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d40484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73881 (p : Pattern) (ha : d16114 p = 1) (hb : d287734 p = 1) : d40588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d287734 q = 1) : d40441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73871 q ha hb
    | true =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d287734 q = 1) : d40442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d287734 q = 1) : d40585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d40585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d40585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d287734 q = 1) : d40586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d40586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d40586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d287734 q = 1) : d40587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d40587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d40587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d287734 q = 1) : d40588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d40588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d40588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73882 (p : Pattern) (ha : d16081 p = 1) (hb : d287734 p = 1) : d40526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d287734 q = 1) : d40279 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73845 q ha hb
    | true =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d287734 q = 1) : d40280 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d287734 q = 1) : d40281 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d40281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d40281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d287734 q = 1) : d40282 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d40282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d40282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d287734 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12495 q = 1) (hb : d287734 q = 1) : d40283 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d40283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d40283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d287734 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16081 q = 1) (hb : d287734 q = 1) : d40526 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d40526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16081, d40526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73883 (p : Pattern) (ha : d23230 p = 1) (hb : d287734 p = 1) : d40516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d287734 q = 1) : d40267 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23228 q = 1) (hb : d287734 q = 1) : d40514 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d40514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23228, d40514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d23229 q = 1) (hb : d287734 q = 1) : d40515 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d40515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23229, d40515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d287734 q = 1) : d20 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d135 q = 1) (hb : d287734 q = 1) : d40154 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5448 q = 1) (hb : d287734 q = 1) : d40276 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d40276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5448, d40276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d5449 q = 1) (hb : d287734 q = 1) : d40277 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d40277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5449, d40277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d23230 q = 1) (hb : d287734 q = 1) : d40516 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23230, d40516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23230, d40516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro73884 (p : Pattern) (ha : d530 p = 1) (hb : d253269 p = 1) : d40492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d528 q = 1) (hb : d253269 q = 1) : d1998 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d310 q = 1) (hb : d253269 q = 1) : d2017 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d529 q = 1) (hb : d253269 q = 1) : d40491 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d529, d40491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d529, d40491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15 q = 1) (hb : d253269 q = 1) : d15 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d130 q = 1) (hb : d253269 q = 1) : d40149 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130, d40149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d311 q = 1) (hb : d253269 q = 1) : d40263 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d40263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d311, d40263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d530 q = 1) (hb : d253269 q = 1) : d40492 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d530, d40492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d530, d40492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro73885 (p : Pattern) (ha : d28739 p = 1) (hb : d253269 p = 1) : d40497 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d310 q = 1) (hb : d253269 q = 1) : d2017 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d534 q = 1) (hb : d253269 q = 1) : d2021 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d534, d2021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d534, d2021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d535 q = 1) (hb : d253269 q = 1) : d40496 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d535, d40496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d535, d40496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9579 q = 1) (hb : d253269 q = 1) : d9579 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d28739 q = 1) (hb : d253269 q = 1) : d40497 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d28739, d40497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28739, d40497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73886 (p : Pattern) (ha : d28745 p = 1) (hb : d287734 p = 1) : d40503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d287734 q = 1) : d40493 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73884 q ha hb
    | true =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d287734 q = 1) : d40494 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d533 q = 1) (hb : d287734 q = 1) : d40495 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28740 q = 1) (hb : d287734 q = 1) : d40498 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28740, d287734, d40498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73885 q ha hb
    | true =>
      simp only [d28740, d287734, d40498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28741 q = 1) (hb : d287734 q = 1) : d40499 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28741, d40499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28741, d40499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d28742 q = 1) (hb : d287734 q = 1) : d40500 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28742, d40500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28742, d40500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28743 q = 1) (hb : d287734 q = 1) : d40501 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28743, d40501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28743, d40501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28744 q = 1) (hb : d287734 q = 1) : d40502 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28744, d40502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28744, d40502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d315 q = 1) (hb : d287734 q = 1) : d40267 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h15 (q : Pattern) (ha : d20 q = 1) (hb : d287734 q = 1) : d20 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d135 q = 1) (hb : d287734 q = 1) : d40154 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d316 q = 1) (hb : d287734 q = 1) : d40268 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d40268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d316, d40268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d317 q = 1) (hb : d287734 q = 1) : d40269 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d40269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d317, d40269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d28745 q = 1) (hb : d287734 q = 1) : d40503 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28745, d40503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28745, d40503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73887 (p : Pattern) (ha : d28750 p = 1) (hb : d287734 p = 1) : d40508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d287734 q = 1) : d40267 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d287734 q = 1) : d20 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d287734 q = 1) : d40154 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d287734 q = 1) : d40268 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d40268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d40268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d317 q = 1) (hb : d287734 q = 1) : d40269 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d40269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d40269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d5448 q = 1) (hb : d287734 q = 1) : d40276 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d40276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d5448, d40276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d5449 q = 1) (hb : d287734 q = 1) : d40277 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d40277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5449, d40277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d28750 q = 1) (hb : d287734 q = 1) : d40508 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28750, d40508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28750, d40508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro73888 (p : Pattern) (ha : d28756 p = 1) (hb : d287734 p = 1) : d40522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d287734 q = 1) : d40504 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73886 q ha hb
    | true =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d287734 q = 1) : d40505 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d287734 q = 1) : d40506 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d40506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d40506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d287734 q = 1) : d40507 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d40507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d40507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28751 q = 1) (hb : d287734 q = 1) : d40509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d40509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73887 q ha hb
    | true =>
      simp only [d28751, d40509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28752 q = 1) (hb : d287734 q = 1) : d40510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d40510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28752, d40510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28753 q = 1) (hb : d287734 q = 1) : d40511 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28753, d40511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28753, d40511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28754 q = 1) (hb : d287734 q = 1) : d40512 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28754, d40512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28754, d40512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28755 q = 1) (hb : d287734 q = 1) : d40513 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28755, d40513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28755, d40513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23231 q = 1) (hb : d287734 q = 1) : d40517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
    | true =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23232 q = 1) (hb : d287734 q = 1) : d40518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23233 q = 1) (hb : d287734 q = 1) : d40519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d40519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d40519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23234 q = 1) (hb : d287734 q = 1) : d40520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d40520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23234, d40520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9382 q = 1) (hb : d287734 q = 1) : d40279 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73845 q ha hb
    | true =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d287734 q = 1) : d40280 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12493 q = 1) (hb : d287734 q = 1) : d40281 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d40281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d40281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12494 q = 1) (hb : d287734 q = 1) : d40282 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d40282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12494, d40282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23235 q = 1) (hb : d287734 q = 1) : d40521 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23235, d40521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23235, d40521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28756 q = 1) (hb : d287734 q = 1) : d40522 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28756, d40522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28756, d40522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73889 (p : Pattern) (ha : d28762 p = 1) (hb : d287734 p = 1) : d40532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28757 q = 1) (hb : d287734 q = 1) : d40523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28757, d40523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73888 q ha hb
    | true =>
      simp only [d28757, d40523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73846 q ha hb
  have h2 (q : Pattern) (ha : d28758 q = 1) (hb : d287734 q = 1) : d40524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28758, d40524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28758, d40524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28759 q = 1) (hb : d287734 q = 1) : d40525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28759, d40525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28759, d40525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d287734 q = 1) : d40527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d40527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73846 q ha hb
    | true =>
      simp only [d16082, d40527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73882 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d287734 q = 1) : d40528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d40528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d40528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d287734 q = 1) : d40529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d40529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d40529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28760 q = 1) (hb : d287734 q = 1) : d40530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28760, d40530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28760, d40530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d287734 q = 1) : d40285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d40285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73846 q ha hb
    | true =>
      simp only [d15967, d40285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73825 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d287734 q = 1) : d40286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d40286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d40286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d287734 q = 1) : d40287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d40287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d40287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d287734 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d287734 q = 1) : d40164 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73825 q ha hb
    | true =>
      simp only [d145, d40164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146 q = 1) (hb : d287734 q = 1) : d40165 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d40165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147 q = 1) (hb : d287734 q = 1) : d40166 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d40166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15970 q = 1) (hb : d287734 q = 1) : d40288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d40288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d40288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28761 q = 1) (hb : d287734 q = 1) : d40531 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28761, d40531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28761, d40531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28762 q = 1) (hb : d287734 q = 1) : d40532 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28762, d40532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28762, d40532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro73890 (p : Pattern) (ha : d28768 p = 1) (hb : d287734 p = 1) : d40538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28763 q = 1) (hb : d287734 q = 1) : d40533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28763, d40533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73889 q ha hb
    | true =>
      simp only [d28763, d40533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28764 q = 1) (hb : d287734 q = 1) : d40534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28764, d40534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28764, d40534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d287734 q = 1) : d40441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73871 q ha hb
    | true =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d287734 q = 1) : d40442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28765 q = 1) (hb : d287734 q = 1) : d40535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28765, d40535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28765, d40535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28766 q = 1) (hb : d287734 q = 1) : d40536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28766, d40536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28766, d40536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28767 q = 1) (hb : d287734 q = 1) : d40537 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28767, d40537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28767, d40537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28768 q = 1) (hb : d287734 q = 1) : d40538 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28768, d40538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28768, d40538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73891 (p : Pattern) (ha : d238875 p = 1) (hb : d287734 p = 1) : d289359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d287734 q = 1) : d40478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d40478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73879 q ha hb
    | true =>
      simp only [d16063, d40478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73877 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d287734 q = 1) : d40479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d40479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d40479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d287734 q = 1) : d40480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d40480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d40480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d287734 q = 1) : d40481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d40481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d40481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d287734 q = 1) : d40488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d40488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73880 q ha hb
    | true =>
      simp only [d16070, d40488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73878 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d287734 q = 1) : d40489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d40489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d40489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d287734 q = 1) : d40490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d40490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d40490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28769 q = 1) (hb : d287734 q = 1) : d40539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28769, d40539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73890 q ha hb
    | true =>
      simp only [d28769, d40539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73872 q ha hb
  have h9 (q : Pattern) (ha : d238871 q = 1) (hb : d287734 q = 1) : d289355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238871, d289355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238871, d289355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d287734 q = 1) : d40589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d40589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73881 q ha hb
    | true =>
      simp only [d16115, d40589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d287734 q = 1) : d40590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d40590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d40590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238872 q = 1) (hb : d287734 q = 1) : d289356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238872, d289356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238872, d289356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238873 q = 1) (hb : d287734 q = 1) : d289357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238873, d289357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238873, d289357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238874 q = 1) (hb : d287734 q = 1) : d289358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238874, d289358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238874, d289358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d238875 q = 1) (hb : d287734 q = 1) : d289359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238875, d289359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238875, d289359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73892 (p : Pattern) (ha : d610 p = 1) (hb : d287734 p = 1) : d40596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d287734 q = 1) : d40451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d287734 q = 1) : d40452 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d40452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d40452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d287734 q = 1) : d40476 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d40476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d40476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d287734 q = 1) : d40596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d40596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d40596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73893 (p : Pattern) (ha : d616 p = 1) (hb : d287734 p = 1) : d40602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d287734 q = 1) : d40451 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d40451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d287734 q = 1) : d40485 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d40485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d40485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d287734 q = 1) : d40486 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d40486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d40486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d287734 q = 1) : d40602 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d40602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d40602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73894 (p : Pattern) (ha : d16121 p = 1) (hb : d287734 p = 1) : d40595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d287734 q = 1) : d40441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73871 q ha hb
    | true =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d287734 q = 1) : d40442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d287734 q = 1) : d40447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d287734 q = 1) : d40448 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d40448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d40448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d287734 q = 1) : d40474 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d40474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d40474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d287734 q = 1) : d40595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d40595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d40595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73895 (p : Pattern) (ha : d16126 p = 1) (hb : d287734 p = 1) : d40601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d287734 q = 1) : d40441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73871 q ha hb
    | true =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d287734 q = 1) : d40442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d287734 q = 1) : d40445 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73863 q ha hb
    | true =>
      simp only [d482, d40445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d287734 q = 1) : d40446 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d40446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d287734 q = 1) : d40447 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d40447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d287734 q = 1) : d40482 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d40482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d40482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d287734 q = 1) : d40483 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d40483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d40483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d287734 q = 1) : d40601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d40601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d40601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73896 (p : Pattern) (ha : d16135 p = 1) (hb : d287734 p = 1) : d40612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d287734 q = 1) : d40441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73871 q ha hb
    | true =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d287734 q = 1) : d40442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d287734 q = 1) : d40585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d40585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d40585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d287734 q = 1) : d40586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d40586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d40586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d287734 q = 1) : d40587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d40587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d40587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d287734 q = 1) : d40612 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d40612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d40612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73897 (p : Pattern) (ha : d28775 p = 1) (hb : d287734 p = 1) : d40606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28763 q = 1) (hb : d287734 q = 1) : d40533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28763, d40533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73889 q ha hb
    | true =>
      simp only [d28763, d40533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28764 q = 1) (hb : d287734 q = 1) : d40534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28764, d40534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28764, d40534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d287734 q = 1) : d40441 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73871 q ha hb
    | true =>
      simp only [d16037, d40441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d287734 q = 1) : d40442 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d40442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28765 q = 1) (hb : d287734 q = 1) : d40535 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28765, d40535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28765, d40535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28766 q = 1) (hb : d287734 q = 1) : d40536 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28766, d40536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28766, d40536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28767 q = 1) (hb : d287734 q = 1) : d40537 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28767, d40537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28767, d40537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28775 q = 1) (hb : d287734 q = 1) : d40606 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28775, d40606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28775, d40606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73898 (p : Pattern) (ha : d238880 p = 1) (hb : d287734 p = 1) : d289364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d287734 q = 1) : d40478 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d40478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73879 q ha hb
    | true =>
      simp only [d16063, d40478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73877 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d287734 q = 1) : d40479 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d40479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d40479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d287734 q = 1) : d40480 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d40480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d40480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d287734 q = 1) : d40481 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d40481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d40481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d287734 q = 1) : d40488 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d40488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73880 q ha hb
    | true =>
      simp only [d16070, d40488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73878 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d287734 q = 1) : d40489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d40489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d40489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d287734 q = 1) : d40490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d40490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d40490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28769 q = 1) (hb : d287734 q = 1) : d40539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28769, d40539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73890 q ha hb
    | true =>
      simp only [d28769, d40539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73872 q ha hb
  have h9 (q : Pattern) (ha : d238871 q = 1) (hb : d287734 q = 1) : d289355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238871, d289355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238871, d289355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d287734 q = 1) : d40589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d40589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73881 q ha hb
    | true =>
      simp only [d16115, d40589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d287734 q = 1) : d40590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d40590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d40590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238872 q = 1) (hb : d287734 q = 1) : d289356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238872, d289356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238872, d289356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238873 q = 1) (hb : d287734 q = 1) : d289357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238873, d289357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238873, d289357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238874 q = 1) (hb : d287734 q = 1) : d289358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238874, d289358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238874, d289358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d287734 q = 1) : d40597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d40597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73894 q ha hb
    | true =>
      simp only [d16122, d40597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73892 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d287734 q = 1) : d40598 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d40598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d40598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d287734 q = 1) : d40599 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d40599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d40599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d287734 q = 1) : d40600 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d40600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d40600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d287734 q = 1) : d40603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d40603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73895 q ha hb
    | true =>
      simp only [d16127, d40603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73893 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d287734 q = 1) : d40604 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d40604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d40604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d287734 q = 1) : d40605 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d40605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d40605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d28776 q = 1) (hb : d287734 q = 1) : d40607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28776, d40607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73897 q ha hb
    | true =>
      simp only [d28776, d40607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73874 q ha hb
  have h23 (q : Pattern) (ha : d238876 q = 1) (hb : d287734 q = 1) : d289360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238876, d289360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d238876, d289360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d287734 q = 1) : d40613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d40613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73896 q ha hb
    | true =>
      simp only [d16136, d40613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d287734 q = 1) : d40614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d40614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d40614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d238877 q = 1) (hb : d287734 q = 1) : d289361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238877, d289361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d238877, d289361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d238878 q = 1) (hb : d287734 q = 1) : d289362 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238878, d289362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238878, d289362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d238879 q = 1) (hb : d287734 q = 1) : d289363 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238879, d289363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d238879, d289363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d238880 q = 1) (hb : d287734 q = 1) : d289364 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238880, d289364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238880, d289364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro73899 (p : Pattern) (ha : d238887 p = 1) (hb : d287734 p = 1) : d289371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28776 q = 1) (hb : d287734 q = 1) : d40607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28776, d40607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73897 q ha hb
    | true =>
      simp only [d28776, d40607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73874 q ha hb
  have h2 (q : Pattern) (ha : d238876 q = 1) (hb : d287734 q = 1) : d289360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238876, d289360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238876, d289360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d287734 q = 1) : d40613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d40613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73896 q ha hb
    | true =>
      simp only [d16136, d40613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d287734 q = 1) : d40614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d40614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d40614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238877 q = 1) (hb : d287734 q = 1) : d289361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238877, d289361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238877, d289361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238885 q = 1) (hb : d287734 q = 1) : d289369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238885, d289369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238885, d289369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238886 q = 1) (hb : d287734 q = 1) : d289370 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238886, d289370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238886, d289370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238887 q = 1) (hb : d287734 q = 1) : d289371 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238887, d289371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238887, d289371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73900 (p : Pattern) (ha : d16176 p = 1) (hb : d287734 p = 1) : d40675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d287734 q = 1) : d40383 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d40383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73857 q ha hb
    | true =>
      simp only [d16005, d40383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73829 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d287734 q = 1) : d40384 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d40384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d40384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d287734 q = 1) : d40385 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d40385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d40385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d287734 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d287734 q = 1) : d40207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73829 q ha hb
    | true =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d287734 q = 1) : d40208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d287734 q = 1) : d40209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d287734 q = 1) : d40386 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d40386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d40386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d287734 q = 1) : d40673 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d40673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d40673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d287734 q = 1) : d40674 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d40674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, d40674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16176 q = 1) (hb : d287734 q = 1) : d40675 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d40675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16176, d40675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro73901 (p : Pattern) (ha : d16186 p = 1) (hb : d287734 p = 1) : d40689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d287734 q = 1) : d40676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d40676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73900 q ha hb
    | true =>
      simp only [d16177, d40676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d287734 q = 1) : d40677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d40677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d40677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d287734 q = 1) : d40684 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d40684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73868 q ha hb
    | true =>
      simp only [d684, d40684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d287734 q = 1) : d40685 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d40685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d40685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d287734 q = 1) : d40686 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d40686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d40686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d287734 q = 1) : d40687 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d40687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d40687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d287734 q = 1) : d40688 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d40688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d40688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d287734 q = 1) : d40689 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d40689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d40689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73902 (p : Pattern) (ha : d16207 p = 1) (hb : d287734 p = 1) : d40728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d287734 q = 1) : d40676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d40676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73900 q ha hb
    | true =>
      simp only [d16177, d40676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d287734 q = 1) : d40677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d40677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d40677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d287734 q = 1) : d40725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d40725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d40725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d287734 q = 1) : d40726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d40726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d40726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d287734 q = 1) : d40727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d40727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d40727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d287734 q = 1) : d40728 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d40728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d40728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73903 (p : Pattern) (ha : d16166 p = 1) (hb : d287734 p = 1) : d40664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d287734 q = 1) : d40377 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d40377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d40377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73845 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d287734 q = 1) : d40279 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73845 q ha hb
    | true =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d287734 q = 1) : d40378 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d40378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d40378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d287734 q = 1) : d40280 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d287734 q = 1) : d40379 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d40379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d40379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d287734 q = 1) : d40380 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d40380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d40380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d287734 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12603 q = 1) (hb : d287734 q = 1) : d40381 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d40381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d40381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d287734 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16166 q = 1) (hb : d287734 q = 1) : d40664 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d40664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16166, d40664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro73904 (p : Pattern) (ha : d28803 p = 1) (hb : d287734 p = 1) : d40660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28794 q = 1) (hb : d287734 q = 1) : d40646 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28794, d40646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28794, d40646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73886 q ha hb
  have h2 (q : Pattern) (ha : d28746 q = 1) (hb : d287734 q = 1) : d40504 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73886 q ha hb
    | true =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28795 q = 1) (hb : d287734 q = 1) : d40647 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28795, d40647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28795, d40647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28747 q = 1) (hb : d287734 q = 1) : d40505 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28796 q = 1) (hb : d287734 q = 1) : d40648 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28796, d40648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28796, d40648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28797 q = 1) (hb : d287734 q = 1) : d40649 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28797, d40649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28797, d40649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28798 q = 1) (hb : d287734 q = 1) : d40650 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28798, d40650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28798, d40650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73887 q ha hb
  have h8 (q : Pattern) (ha : d28751 q = 1) (hb : d287734 q = 1) : d40509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d40509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73887 q ha hb
    | true =>
      simp only [d28751, d40509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28799 q = 1) (hb : d287734 q = 1) : d40651 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28799, d40651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28799, d40651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28752 q = 1) (hb : d287734 q = 1) : d40510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d40510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28752, d40510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28800 q = 1) (hb : d287734 q = 1) : d40652 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28800, d40652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28800, d40652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28801 q = 1) (hb : d287734 q = 1) : d40653 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28801, d40653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28801, d40653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28802 q = 1) (hb : d287734 q = 1) : d40654 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28802, d40654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28802, d40654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23310 q = 1) (hb : d287734 q = 1) : d40655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d40655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d40655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
  have h15 (q : Pattern) (ha : d23231 q = 1) (hb : d287734 q = 1) : d40517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
    | true =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23311 q = 1) (hb : d287734 q = 1) : d40656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d40656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23311, d40656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23232 q = 1) (hb : d287734 q = 1) : d40518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23312 q = 1) (hb : d287734 q = 1) : d40657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d40657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23312, d40657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23313 q = 1) (hb : d287734 q = 1) : d40658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d40658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23313, d40658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12599 q = 1) (hb : d287734 q = 1) : d40377 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d40377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d40377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73845 q ha hb
  have h21 (q : Pattern) (ha : d9382 q = 1) (hb : d287734 q = 1) : d40279 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73845 q ha hb
    | true =>
      simp only [d9382, d40279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12600 q = 1) (hb : d287734 q = 1) : d40378 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d40378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12600, d40378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9384 q = 1) (hb : d287734 q = 1) : d40280 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9384, d40280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12601 q = 1) (hb : d287734 q = 1) : d40379 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d40379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12601, d40379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12602 q = 1) (hb : d287734 q = 1) : d40380 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d40380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12602, d40380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d23314 q = 1) (hb : d287734 q = 1) : d40659 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23314, d40659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d23314, d40659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d28803 q = 1) (hb : d287734 q = 1) : d40660 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28803, d40660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28803, d40660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro73905 (p : Pattern) (ha : d28809 p = 1) (hb : d287734 p = 1) : d40670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28804 q = 1) (hb : d287734 q = 1) : d40661 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28804, d40661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73904 q ha hb
    | true =>
      simp only [d28804, d40661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73857 q ha hb
  have h2 (q : Pattern) (ha : d28805 q = 1) (hb : d287734 q = 1) : d40662 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28805, d40662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28805, d40662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28806 q = 1) (hb : d287734 q = 1) : d40663 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28806, d40663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28806, d40663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d287734 q = 1) : d40665 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d40665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73857 q ha hb
    | true =>
      simp only [d16167, d40665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73903 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d287734 q = 1) : d40666 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d40666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d40666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d287734 q = 1) : d40667 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d40667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d40667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28807 q = 1) (hb : d287734 q = 1) : d40668 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28807, d40668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28807, d40668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d287734 q = 1) : d40383 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d40383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73857 q ha hb
    | true =>
      simp only [d16005, d40383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73829 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d287734 q = 1) : d40384 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d40384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d40384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d287734 q = 1) : d40385 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d40385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d40385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d287734 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d232 q = 1) (hb : d287734 q = 1) : d40207 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73829 q ha hb
    | true =>
      simp only [d232, d40207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d287734 q = 1) : d40208 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d40208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d287734 q = 1) : d40209 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d40209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d287734 q = 1) : d40386 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d40386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d40386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28808 q = 1) (hb : d287734 q = 1) : d40669 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28808, d40669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28808, d40669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28809 q = 1) (hb : d287734 q = 1) : d40670 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28809, d40670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28809, d40670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro73906 (p : Pattern) (ha : d28815 p = 1) (hb : d287734 p = 1) : d40681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28810 q = 1) (hb : d287734 q = 1) : d40671 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28810, d40671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73905 q ha hb
    | true =>
      simp only [d28810, d40671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28811 q = 1) (hb : d287734 q = 1) : d40672 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28811, d40672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28811, d40672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d287734 q = 1) : d40676 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d40676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73900 q ha hb
    | true =>
      simp only [d16177, d40676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d287734 q = 1) : d40677 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d40677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d40677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28812 q = 1) (hb : d287734 q = 1) : d40678 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28812, d40678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28812, d40678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28813 q = 1) (hb : d287734 q = 1) : d40679 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28813, d40679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28813, d40679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28814 q = 1) (hb : d287734 q = 1) : d40680 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28814, d40680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28814, d40680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28815 q = 1) (hb : d287734 q = 1) : d40681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28815, d40681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28815, d40681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73907 (p : Pattern) (ha : d238897 p = 1) (hb : d287734 p = 1) : d289381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28816 q = 1) (hb : d287734 q = 1) : d40690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28816, d40690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73906 q ha hb
    | true =>
      simp only [d28816, d40690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73901 q ha hb
  have h2 (q : Pattern) (ha : d238893 q = 1) (hb : d287734 q = 1) : d289377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238893, d289377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238893, d289377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d287734 q = 1) : d40729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d40729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73902 q ha hb
    | true =>
      simp only [d16208, d40729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d287734 q = 1) : d40730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d40730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d40730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238894 q = 1) (hb : d287734 q = 1) : d289378 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238894, d289378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238894, d289378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238895 q = 1) (hb : d287734 q = 1) : d289379 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238895, d289379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238895, d289379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238896 q = 1) (hb : d287734 q = 1) : d289380 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238896, d289380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238896, d289380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238897 q = 1) (hb : d287734 q = 1) : d289381 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238897, d289381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238897, d289381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73908 (p : Pattern) (ha : d238903 p = 1) (hb : d287734 p = 1) : d289387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d287734 q = 1) : d40461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d40461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d40461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73873 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d287734 q = 1) : d40462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d40462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d40462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d287734 q = 1) : d40471 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d40471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73873 q ha hb
    | true =>
      simp only [d16058, d40471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73875 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d287734 q = 1) : d40472 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d40472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d40472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d287734 q = 1) : d40473 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d40473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d40473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238881 q = 1) (hb : d287734 q = 1) : d289365 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238881, d289365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73891 q ha hb
    | true =>
      simp only [d238881, d289365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73898 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d287734 q = 1) : d40632 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d40632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73876 q ha hb
    | true =>
      simp only [d16144, d40632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73866 q ha hb
  have h8 (q : Pattern) (ha : d238882 q = 1) (hb : d287734 q = 1) : d289366 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238882, d289366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238882, d289366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238883 q = 1) (hb : d287734 q = 1) : d289367 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238883, d289367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238883, d289367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d238884 q = 1) (hb : d287734 q = 1) : d289368 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238884, d289368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238884, d289368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d238888 q = 1) (hb : d287734 q = 1) : d289372 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238888, d289372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238888, d289372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73899 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d287734 q = 1) : d40641 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d40641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d40641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73867 q ha hb
  have h13 (q : Pattern) (ha : d238889 q = 1) (hb : d287734 q = 1) : d289373 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238889, d289373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d238889, d289373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238890 q = 1) (hb : d287734 q = 1) : d289374 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238890, d289374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238890, d289374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d238891 q = 1) (hb : d287734 q = 1) : d289375 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238891, d289375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238891, d289375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d238892 q = 1) (hb : d287734 q = 1) : d289376 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238892, d289376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238892, d289376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238898 q = 1) (hb : d287734 q = 1) : d289382 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238898, d289382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238898, d289382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73907 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d287734 q = 1) : d40746 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d40746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d40746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73870 q ha hb
  have h19 (q : Pattern) (ha : d238899 q = 1) (hb : d287734 q = 1) : d289383 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238899, d289383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238899, d289383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d238900 q = 1) (hb : d287734 q = 1) : d289384 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238900, d289384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d238900, d289384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d238901 q = 1) (hb : d287734 q = 1) : d289385 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238901, d289385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d238901, d289385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d238902 q = 1) (hb : d287734 q = 1) : d289386 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238902, d289386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238902, d289386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d238903 q = 1) (hb : d287734 q = 1) : d289387 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238903, d289387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238903, d289387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro73909 (p : Pattern) (ha : d238909 p = 1) (hb : d287734 p = 1) : d289393 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238904 q = 1) (hb : d287734 q = 1) : d289388 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238904, d289388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238904, d289388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73908 q ha hb
  have h2 (q : Pattern) (ha : d238905 q = 1) (hb : d287734 q = 1) : d289389 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238905, d289389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238905, d289389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238906 q = 1) (hb : d287734 q = 1) : d289390 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238906, d289390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238906, d289390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238907 q = 1) (hb : d287734 q = 1) : d289391 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238907, d289391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238907, d289391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238908 q = 1) (hb : d287734 q = 1) : d289392 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238908, d289392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238908, d289392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238909 q = 1) (hb : d287734 q = 1) : d289393 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238909, d289393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238909, d289393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73910 (p : Pattern) (ha : d750 p = 1) (hb : d287734 p = 1) : d40759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d287734 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d287734 q = 1) : d40154 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d287734 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d287734 q = 1) : d40155 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d40155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136, d40155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137 q = 1) (hb : d287734 q = 1) : d40156 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d40156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d40156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d750 q = 1) (hb : d287734 q = 1) : d40759 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, d40759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d750, d40759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h9 p ha hb
theorem andIntro73911 (p : Pattern) (ha : d758 p = 1) (hb : d287734 p = 1) : d40768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d287734 q = 1) : d40271 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d40271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73844 q ha hb
    | true =>
      simp only [d319, d40271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d287734 q = 1) : d40272 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d40272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d40272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d287734 q = 1) : d40273 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d40273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d40273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d287734 q = 1) : d40274 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d40274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d40274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d287734 q = 1) : d40760 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
    | true =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d287734 q = 1) : d40761 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d287734 q = 1) : d40762 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d40762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d40762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d287734 q = 1) : d40763 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d40763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d40763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d287734 q = 1) : d40766 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d40766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d40766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d287734 q = 1) : d40767 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d40767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d40767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d758 q = 1) (hb : d287734 q = 1) : d40768 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d40768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d758, d40768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73912 (p : Pattern) (ha : d762 p = 1) (hb : d287734 p = 1) : d40772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d287734 q = 1) : d40760 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
    | true =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d287734 q = 1) : d40761 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d287734 q = 1) : d40762 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d40762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d40762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d287734 q = 1) : d40763 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d40763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d40763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d287734 q = 1) : d40767 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d40767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d40767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d287734 q = 1) : d40772 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d40772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, d40772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73913 (p : Pattern) (ha : d773 p = 1) (hb : d287734 p = 1) : d40783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d287734 q = 1) : d40773 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d40773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73911 q ha hb
    | true =>
      simp only [d763, d40773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73912 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d287734 q = 1) : d40774 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d40774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d40774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d287734 q = 1) : d40775 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d40775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d40775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d287734 q = 1) : d40777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d40777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d40777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d772 q = 1) (hb : d287734 q = 1) : d40782 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d40782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, d40782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d773 q = 1) (hb : d287734 q = 1) : d40783 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d40783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d773, d40783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73914 (p : Pattern) (ha : d783 p = 1) (hb : d287734 p = 1) : d40793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d287734 q = 1) : d40790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d287734 q = 1) : d40791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d40791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d40791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d287734 q = 1) : d40792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d40792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d40792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d287734 q = 1) : d40793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d40793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d40793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73915 (p : Pattern) (ha : d793 p = 1) (hb : d287734 p = 1) : d40803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d287734 q = 1) : d40790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d287734 q = 1) : d40791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d40791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d40791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d287734 q = 1) : d40792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d40792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d40792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d287734 q = 1) : d40803 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d40803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d40803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73916 (p : Pattern) (ha : d950 p = 1) (hb : d287734 p = 1) : d40995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d287734 q = 1) : d40984 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d40984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73914 q ha hb
    | true =>
      simp only [d939, d40984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d287734 q = 1) : d40985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d40985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d40985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d287734 q = 1) : d40986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d40986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d40986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d287734 q = 1) : d40987 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d40987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d40987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d287734 q = 1) : d40988 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d40988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d40988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d287734 q = 1) : d40990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d40990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73915 q ha hb
    | true =>
      simp only [d945, d40990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d287734 q = 1) : d40991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d40991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d40991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d287734 q = 1) : d40992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d40992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d40992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d287734 q = 1) : d40993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d40993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d40993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d287734 q = 1) : d40994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d40994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d40994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d287734 q = 1) : d40995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d40995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d40995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73917 (p : Pattern) (ha : d959 p = 1) (hb : d287734 p = 1) : d41004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d287734 q = 1) : d40990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d40990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73915 q ha hb
    | true =>
      simp only [d945, d40990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d287734 q = 1) : d40991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d40991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d40991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d287734 q = 1) : d40992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d40992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d40992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d287734 q = 1) : d40993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d40993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d40993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d287734 q = 1) : d40994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d40994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d40994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d287734 q = 1) : d41004 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d41004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d41004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73918 (p : Pattern) (ha : d981 p = 1) (hb : d287734 p = 1) : d41041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d287734 q = 1) : d40372 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d40372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d40372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73844 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d287734 q = 1) : d40271 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d40271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73844 q ha hb
    | true =>
      simp only [d319, d40271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d287734 q = 1) : d40373 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d40373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d40373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d287734 q = 1) : d40272 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d40272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d40272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d287734 q = 1) : d40374 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d40374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d40374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d287734 q = 1) : d40375 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d40375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d40375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d287734 q = 1) : d41025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d41025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d41025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d287734 q = 1) : d40760 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
    | true =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d287734 q = 1) : d41026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d41026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d41026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d287734 q = 1) : d40761 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d287734 q = 1) : d41027 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d41027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d41027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d287734 q = 1) : d41028 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d41028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d41028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d287734 q = 1) : d41040 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d41040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d41040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d287734 q = 1) : d41034 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d41034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d41034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d981 q = 1) (hb : d287734 q = 1) : d41041 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d41041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d981, d41041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73919 (p : Pattern) (ha : d986 p = 1) (hb : d287734 p = 1) : d41045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d287734 q = 1) : d41025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d41025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d41025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d287734 q = 1) : d40760 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
    | true =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d287734 q = 1) : d41026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d41026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d41026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d287734 q = 1) : d40761 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d287734 q = 1) : d41027 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d41027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d41027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d287734 q = 1) : d41028 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d41028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d41028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d287734 q = 1) : d41034 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d41034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d41034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d986 q = 1) (hb : d287734 q = 1) : d41045 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d41045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d986, d41045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73920 (p : Pattern) (ha : d1005 p = 1) (hb : d287734 p = 1) : d41064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d287734 q = 1) : d41046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d41046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73918 q ha hb
    | true =>
      simp only [d987, d41046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73919 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d287734 q = 1) : d41047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d41047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d41047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d287734 q = 1) : d41048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d41048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d41048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d287734 q = 1) : d41054 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d41054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d41054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d287734 q = 1) : d41063 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d41063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d41063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1005 q = 1) (hb : d287734 q = 1) : d41064 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d41064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1005, d41064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73921 (p : Pattern) (ha : d1063 p = 1) (hb : d287734 p = 1) : d41135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d287734 q = 1) : d41065 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d41065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73920 q ha hb
    | true =>
      simp only [d1006, d41065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d287734 q = 1) : d41066 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d41066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d41066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d287734 q = 1) : d41132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d41132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d41132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d287734 q = 1) : d41133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d41133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d41133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d287734 q = 1) : d41134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d41134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d41134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d287734 q = 1) : d41135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d41135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d41135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73922 (p : Pattern) (ha : d1069 p = 1) (hb : d287734 p = 1) : d41141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d287734 q = 1) : d41136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d41136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73921 q ha hb
    | true =>
      simp only [d1064, d41136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d287734 q = 1) : d41137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d41137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d41137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d287734 q = 1) : d41138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d41138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d41138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d287734 q = 1) : d41139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d41139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d41139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d287734 q = 1) : d41140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d41140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d41140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d287734 q = 1) : d41141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d41141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d41141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73923 (p : Pattern) (ha : d28836 p = 1) (hb : d287734 p = 1) : d40765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d287734 q = 1) : d40504 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73886 q ha hb
    | true =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d287734 q = 1) : d40505 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d287734 q = 1) : d40506 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d40506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d40506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d287734 q = 1) : d40507 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d40507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d40507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28751 q = 1) (hb : d287734 q = 1) : d40509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d40509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73887 q ha hb
    | true =>
      simp only [d28751, d40509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28752 q = 1) (hb : d287734 q = 1) : d40510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d40510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28752, d40510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28753 q = 1) (hb : d287734 q = 1) : d40511 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28753, d40511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28753, d40511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28754 q = 1) (hb : d287734 q = 1) : d40512 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28754, d40512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28754, d40512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28755 q = 1) (hb : d287734 q = 1) : d40513 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28755, d40513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28755, d40513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23231 q = 1) (hb : d287734 q = 1) : d40517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
    | true =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23232 q = 1) (hb : d287734 q = 1) : d40518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23233 q = 1) (hb : d287734 q = 1) : d40519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d40519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d40519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23234 q = 1) (hb : d287734 q = 1) : d40520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d40520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23234, d40520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d751 q = 1) (hb : d287734 q = 1) : d40760 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
    | true =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d287734 q = 1) : d40761 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d753 q = 1) (hb : d287734 q = 1) : d40762 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d40762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d40762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d754 q = 1) (hb : d287734 q = 1) : d40763 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d40763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d754, d40763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d28835 q = 1) (hb : d287734 q = 1) : d40764 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28835, d40764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28835, d40764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28836 q = 1) (hb : d287734 q = 1) : d40765 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28836, d40765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28836, d40765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73924 (p : Pattern) (ha : d28842 p = 1) (hb : d287734 p = 1) : d40779 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28837 q = 1) (hb : d287734 q = 1) : d40769 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28837, d40769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73923 q ha hb
    | true =>
      simp only [d28837, d40769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73911 q ha hb
  have h2 (q : Pattern) (ha : d28838 q = 1) (hb : d287734 q = 1) : d40770 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28838, d40770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28838, d40770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28839 q = 1) (hb : d287734 q = 1) : d40771 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28839, d40771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28839, d40771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d287734 q = 1) : d40773 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d40773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73911 q ha hb
    | true =>
      simp only [d763, d40773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73912 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d287734 q = 1) : d40774 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d40774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d40774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d287734 q = 1) : d40775 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d40775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d40775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28840 q = 1) (hb : d287734 q = 1) : d40776 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28840, d40776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28840, d40776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d287734 q = 1) : d40777 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d40777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d40777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28841 q = 1) (hb : d287734 q = 1) : d40778 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28841, d40778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28841, d40778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28842 q = 1) (hb : d287734 q = 1) : d40779 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28842, d40779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28842, d40779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro73925 (p : Pattern) (ha : d28848 p = 1) (hb : d287734 p = 1) : d40789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d287734 q = 1) : d40780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73924 q ha hb
    | true =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d287734 q = 1) : d40781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d287734 q = 1) : d40786 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d287734 q = 1) : d40787 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d40787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d40787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28847 q = 1) (hb : d287734 q = 1) : d40788 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28847, d40788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28847, d40788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28848 q = 1) (hb : d287734 q = 1) : d40789 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28848, d40789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28848, d40789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73926 (p : Pattern) (ha : d28854 p = 1) (hb : d287734 p = 1) : d40799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d287734 q = 1) : d40794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d40794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73925 q ha hb
    | true =>
      simp only [d28849, d40794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73914 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d287734 q = 1) : d40795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d40795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d40795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d287734 q = 1) : d40796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d40796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d40796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d287734 q = 1) : d40797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d40797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d40797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d287734 q = 1) : d40798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d40798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d40798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28854 q = 1) (hb : d287734 q = 1) : d40799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28854, d40799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28854, d40799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73927 (p : Pattern) (ha : d28857 p = 1) (hb : d287734 p = 1) : d40802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d287734 q = 1) : d40780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73924 q ha hb
    | true =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d287734 q = 1) : d40781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d287734 q = 1) : d40786 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d287734 q = 1) : d40787 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d40787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d40787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28847 q = 1) (hb : d287734 q = 1) : d40788 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28847, d40788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28847, d40788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28857 q = 1) (hb : d287734 q = 1) : d40802 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28857, d40802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28857, d40802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73928 (p : Pattern) (ha : d28863 p = 1) (hb : d287734 p = 1) : d40809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d287734 q = 1) : d40794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d40794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73925 q ha hb
    | true =>
      simp only [d28849, d40794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73914 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d287734 q = 1) : d40795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d40795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d40795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d287734 q = 1) : d40796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d40796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d40796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d287734 q = 1) : d40797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d40797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d40797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d287734 q = 1) : d40798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d40798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d40798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28858 q = 1) (hb : d287734 q = 1) : d40804 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28858, d40804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73927 q ha hb
    | true =>
      simp only [d28858, d40804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73915 q ha hb
  have h7 (q : Pattern) (ha : d28859 q = 1) (hb : d287734 q = 1) : d40805 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28859, d40805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28859, d40805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28860 q = 1) (hb : d287734 q = 1) : d40806 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28860, d40806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28860, d40806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28861 q = 1) (hb : d287734 q = 1) : d40807 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28861, d40807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28861, d40807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28862 q = 1) (hb : d287734 q = 1) : d40808 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28862, d40808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28862, d40808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28863 q = 1) (hb : d287734 q = 1) : d40809 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28863, d40809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28863, d40809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73929 (p : Pattern) (ha : d28985 p = 1) (hb : d287734 p = 1) : d40989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28849 q = 1) (hb : d287734 q = 1) : d40794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28849, d40794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73925 q ha hb
    | true =>
      simp only [d28849, d40794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73914 q ha hb
  have h2 (q : Pattern) (ha : d28850 q = 1) (hb : d287734 q = 1) : d40795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28850, d40795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28850, d40795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28851 q = 1) (hb : d287734 q = 1) : d40796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28851, d40796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28851, d40796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28852 q = 1) (hb : d287734 q = 1) : d40797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28852, d40797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28852, d40797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28853 q = 1) (hb : d287734 q = 1) : d40798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d28853, d40798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28853, d40798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d287734 q = 1) : d40984 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d40984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73914 q ha hb
    | true =>
      simp only [d939, d40984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d287734 q = 1) : d40985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d40985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d40985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d287734 q = 1) : d40986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d40986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d40986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d287734 q = 1) : d40987 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d40987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d40987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d287734 q = 1) : d40988 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d40988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d40988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d28985 q = 1) (hb : d287734 q = 1) : d40989 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d28985, d40989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28985, d40989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73930 (p : Pattern) (ha : d806 p = 1) (hb : d287734 p = 1) : d40816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d287734 q = 1) : d40790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d287734 q = 1) : d40791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d40791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d40791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d287734 q = 1) : d40815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d40815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d40815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d287734 q = 1) : d40816 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d40816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d40816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73931 (p : Pattern) (ha : d816 p = 1) (hb : d287734 p = 1) : d40826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d287734 q = 1) : d40790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d287734 q = 1) : d40824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d40824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d40824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d287734 q = 1) : d40825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d40825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d40825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d287734 q = 1) : d40826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d40826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d40826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73932 (p : Pattern) (ha : d28868 p = 1) (hb : d287734 p = 1) : d40814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d287734 q = 1) : d40780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73924 q ha hb
    | true =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d287734 q = 1) : d40781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d287734 q = 1) : d40786 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d287734 q = 1) : d40787 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d40787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d40787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28867 q = 1) (hb : d287734 q = 1) : d40813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28867, d40813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28867, d40813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28868 q = 1) (hb : d287734 q = 1) : d40814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28868, d40814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28868, d40814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73933 (p : Pattern) (ha : d28875 p = 1) (hb : d287734 p = 1) : d40823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d287734 q = 1) : d40780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73924 q ha hb
    | true =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d287734 q = 1) : d40781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d287734 q = 1) : d40786 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28873 q = 1) (hb : d287734 q = 1) : d40821 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28873, d40821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28873, d40821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28874 q = 1) (hb : d287734 q = 1) : d40822 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28874, d40822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28874, d40822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28875 q = 1) (hb : d287734 q = 1) : d40823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28875, d40823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28875, d40823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73934 (p : Pattern) (ha : d23421 p = 1) (hb : d287734 p = 1) : d40858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d287734 q = 1) : d40493 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73884 q ha hb
    | true =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d287734 q = 1) : d40494 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d533 q = 1) (hb : d287734 q = 1) : d40495 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23419 q = 1) (hb : d287734 q = 1) : d40856 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d40856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23419, d40856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d23420 q = 1) (hb : d287734 q = 1) : d40857 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d40857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23420, d40857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d315 q = 1) (hb : d287734 q = 1) : d40267 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23228 q = 1) (hb : d287734 q = 1) : d40514 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d40514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23228, d40514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d23229 q = 1) (hb : d287734 q = 1) : d40515 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d40515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23229, d40515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d23421 q = 1) (hb : d287734 q = 1) : d40858 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23421, d40858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23421, d40858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro73935 (p : Pattern) (ha : d821 p = 1) (hb : d253269 p = 1) : d40830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d528 q = 1) (hb : d253269 q = 1) : d1998 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d820 q = 1) (hb : d253269 q = 1) : d1999 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d820, d1999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d820, d1999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d128 q = 1) : d128 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d129 q = 1) (hb : d253269 q = 1) : d2016 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d129, d253269, d2016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d310 q = 1) (hb : d253269 q = 1) : d2017 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310, d2017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d529 q = 1) (hb : d253269 q = 1) : d40491 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d529, d40491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d529, d40491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d821 q = 1) (hb : d253269 q = 1) : d40830 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d821, d40830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d821, d40830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73936 (p : Pattern) (ha : d28879 p = 1) (hb : d253269 p = 1) : d32701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d528 q = 1) (hb : d253269 q = 1) : d1998 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d825 q = 1) (hb : d253269 q = 1) : d2013 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d825, d2013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d825, d2013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d826 q = 1) (hb : d253269 q = 1) : d2014 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d826, d2014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d826, d2014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28879 q = 1) (hb : d253269 q = 1) : d32701 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d28879, d32701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28879, d32701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro73937 (p : Pattern) (ha : d28882 p = 1) (hb : d253269 p = 1) : d40836 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1519 q = 1) (hb : d253269 q = 1) : d1519 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1520 q = 1) (hb : d253269 q = 1) : d40834 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1520, d40834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1520, d40834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1531 q = 1) (hb : d253269 q = 1) : d1531 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1532 q = 1) (hb : d253269 q = 1) : d40835 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1532, d40835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1532, d40835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9579 q = 1) (hb : d253269 q = 1) : d9579 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d28882 q = 1) (hb : d253269 q = 1) : d40836 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d28882, d40836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28882, d40836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73938 (p : Pattern) (ha : d28891 p = 1) (hb : d287734 p = 1) : d40845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d287734 q = 1) : d40831 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d287734, d40831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73935 q ha hb
    | true =>
      simp only [d822, d287734, d40831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d287734 q = 1) : d40832 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d40832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d40832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d531 q = 1) (hb : d287734 q = 1) : d40493 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73884 q ha hb
    | true =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d532 q = 1) (hb : d287734 q = 1) : d40494 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d824 q = 1) (hb : d287734 q = 1) : d40833 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d40833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d824, d40833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28880 q = 1) (hb : d287734 q = 1) : d32702 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28880, d287734, d32702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73936 q ha hb
    | true =>
      simp only [d28880, d287734, d32702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28881 q = 1) (hb : d287734 q = 1) : d32703 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28881, d32703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28881, d32703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d28883 q = 1) (hb : d287734 q = 1) : d40837 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28883, d287734, d40837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73937 q ha hb
    | true =>
      simp only [d28883, d287734, d40837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28884 q = 1) (hb : d287734 q = 1) : d40838 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28884, d40838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28884, d40838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d28885 q = 1) (hb : d287734 q = 1) : d40839 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28885, d40839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28885, d40839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28886 q = 1) (hb : d287734 q = 1) : d40840 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28886, d40840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28886, d40840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28887 q = 1) (hb : d287734 q = 1) : d40841 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28887, d40841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28887, d40841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d533 q = 1) (hb : d287734 q = 1) : d40495 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d28888 q = 1) (hb : d287734 q = 1) : d40842 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28888, d40842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28888, d40842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d28889 q = 1) (hb : d287734 q = 1) : d40843 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28889, d40843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28889, d40843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d28890 q = 1) (hb : d287734 q = 1) : d40844 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28890, d40844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d28890, d40844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h22 (q : Pattern) (ha : d28891 q = 1) (hb : d287734 q = 1) : d40845 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28891, d40845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28891, d40845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro73939 (p : Pattern) (ha : d28896 p = 1) (hb : d287734 p = 1) : d40850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d287734 q = 1) : d40493 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73884 q ha hb
    | true =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d287734 q = 1) : d40494 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d533 q = 1) (hb : d287734 q = 1) : d40495 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28740 q = 1) (hb : d287734 q = 1) : d40498 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28740, d287734, d40498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73885 q ha hb
    | true =>
      simp only [d28740, d287734, d40498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28741 q = 1) (hb : d287734 q = 1) : d40499 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28741, d40499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28741, d40499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d28742 q = 1) (hb : d287734 q = 1) : d40500 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28742, d40500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28742, d40500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28743 q = 1) (hb : d287734 q = 1) : d40501 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28743, d40501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28743, d40501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28744 q = 1) (hb : d287734 q = 1) : d40502 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28744, d40502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28744, d40502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d315 q = 1) (hb : d287734 q = 1) : d40267 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h15 (q : Pattern) (ha : d23228 q = 1) (hb : d287734 q = 1) : d40514 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23228, d40514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23228, d40514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d23229 q = 1) (hb : d287734 q = 1) : d40515 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23229, d40515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23229, d40515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d28896 q = 1) (hb : d287734 q = 1) : d40850 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d28896, d40850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d28896, d40850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro73940 (p : Pattern) (ha : d28902 p = 1) (hb : d287734 p = 1) : d40864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28892 q = 1) (hb : d287734 q = 1) : d40846 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28892, d40846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73938 q ha hb
    | true =>
      simp only [d28892, d40846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28893 q = 1) (hb : d287734 q = 1) : d40847 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28893, d40847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28893, d40847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28894 q = 1) (hb : d287734 q = 1) : d40848 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28894, d40848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28894, d40848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28895 q = 1) (hb : d287734 q = 1) : d40849 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28895, d40849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28895, d40849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28897 q = 1) (hb : d287734 q = 1) : d40851 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28897, d40851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73939 q ha hb
    | true =>
      simp only [d28897, d40851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28898 q = 1) (hb : d287734 q = 1) : d40852 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28898, d40852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28898, d40852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28899 q = 1) (hb : d287734 q = 1) : d40853 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28899, d40853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28899, d40853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28900 q = 1) (hb : d287734 q = 1) : d40854 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28900, d40854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28900, d40854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28901 q = 1) (hb : d287734 q = 1) : d40855 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28901, d40855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28901, d40855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23422 q = 1) (hb : d287734 q = 1) : d40859 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d40859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73934 q ha hb
    | true =>
      simp only [d23422, d40859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23423 q = 1) (hb : d287734 q = 1) : d40860 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d40860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23423, d40860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23424 q = 1) (hb : d287734 q = 1) : d40861 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d40861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d40861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23425 q = 1) (hb : d287734 q = 1) : d40862 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d40862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23425, d40862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23231 q = 1) (hb : d287734 q = 1) : d40517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
    | true =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d23232 q = 1) (hb : d287734 q = 1) : d40518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23233 q = 1) (hb : d287734 q = 1) : d40519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d40519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d40519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23234 q = 1) (hb : d287734 q = 1) : d40520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d40520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23234, d40520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23426 q = 1) (hb : d287734 q = 1) : d40863 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23426, d40863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23426, d40863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28902 q = 1) (hb : d287734 q = 1) : d40864 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28902, d40864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28902, d40864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73941 (p : Pattern) (ha : d28906 p = 1) (hb : d287734 p = 1) : d40868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23231 q = 1) (hb : d287734 q = 1) : d40517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
    | true =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23232 q = 1) (hb : d287734 q = 1) : d40518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23233 q = 1) (hb : d287734 q = 1) : d40519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23233, d40519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23233, d40519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23234 q = 1) (hb : d287734 q = 1) : d40520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23234, d40520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23234, d40520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d287734 q = 1) : d40760 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
    | true =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d287734 q = 1) : d40761 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d287734 q = 1) : d40762 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d40762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d40762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d287734 q = 1) : d40763 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d40763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d40763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28835 q = 1) (hb : d287734 q = 1) : d40764 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28835, d40764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28835, d40764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d287734 q = 1) : d40767 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d40767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d40767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28906 q = 1) (hb : d287734 q = 1) : d40868 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d28906, d40868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28906, d40868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73942 (p : Pattern) (ha : d28912 p = 1) (hb : d287734 p = 1) : d40874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28903 q = 1) (hb : d287734 q = 1) : d40865 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28903, d40865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73940 q ha hb
    | true =>
      simp only [d28903, d40865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73923 q ha hb
  have h2 (q : Pattern) (ha : d28904 q = 1) (hb : d287734 q = 1) : d40866 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28904, d40866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28904, d40866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28905 q = 1) (hb : d287734 q = 1) : d40867 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28905, d40867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28905, d40867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28907 q = 1) (hb : d287734 q = 1) : d40869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28907, d40869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73923 q ha hb
    | true =>
      simp only [d28907, d40869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73941 q ha hb
  have h5 (q : Pattern) (ha : d28908 q = 1) (hb : d287734 q = 1) : d40870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28908, d40870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28908, d40870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28909 q = 1) (hb : d287734 q = 1) : d40871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28909, d40871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28909, d40871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28910 q = 1) (hb : d287734 q = 1) : d40872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28910, d40872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28910, d40872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28837 q = 1) (hb : d287734 q = 1) : d40769 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d28837, d40769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73923 q ha hb
    | true =>
      simp only [d28837, d40769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73911 q ha hb
  have h9 (q : Pattern) (ha : d28838 q = 1) (hb : d287734 q = 1) : d40770 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d28838, d40770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28838, d40770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28839 q = 1) (hb : d287734 q = 1) : d40771 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d28839, d40771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28839, d40771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d763 q = 1) (hb : d287734 q = 1) : d40773 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d40773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73911 q ha hb
    | true =>
      simp only [d763, d40773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73912 q ha hb
  have h12 (q : Pattern) (ha : d764 q = 1) (hb : d287734 q = 1) : d40774 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d40774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d40774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d765 q = 1) (hb : d287734 q = 1) : d40775 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d40775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d40775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d28840 q = 1) (hb : d287734 q = 1) : d40776 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d28840, d40776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28840, d40776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28911 q = 1) (hb : d287734 q = 1) : d40873 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d28911, d40873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28911, d40873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d28912 q = 1) (hb : d287734 q = 1) : d40874 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d28912, d40874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d28912, d40874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro73943 (p : Pattern) (ha : d28918 p = 1) (hb : d287734 p = 1) : d40880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28913 q = 1) (hb : d287734 q = 1) : d40875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28913, d40875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73942 q ha hb
    | true =>
      simp only [d28913, d40875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28914 q = 1) (hb : d287734 q = 1) : d40876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28914, d40876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28914, d40876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28843 q = 1) (hb : d287734 q = 1) : d40780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73924 q ha hb
    | true =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28844 q = 1) (hb : d287734 q = 1) : d40781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28915 q = 1) (hb : d287734 q = 1) : d40877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28915, d40877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28915, d40877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28916 q = 1) (hb : d287734 q = 1) : d40878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28916, d40878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28916, d40878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28917 q = 1) (hb : d287734 q = 1) : d40879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28917, d40879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28917, d40879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28918 q = 1) (hb : d287734 q = 1) : d40880 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28918, d40880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28918, d40880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73944 (p : Pattern) (ha : d28956 p = 1) (hb : d287734 p = 1) : d40952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d287734 q = 1) : d40780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73924 q ha hb
    | true =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d287734 q = 1) : d40781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28953 q = 1) (hb : d287734 q = 1) : d40949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28953, d40949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28953, d40949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28954 q = 1) (hb : d287734 q = 1) : d40950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28954, d40950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28954, d40950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28955 q = 1) (hb : d287734 q = 1) : d40951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28955, d40951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28955, d40951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28956 q = 1) (hb : d287734 q = 1) : d40952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28956, d40952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28956, d40952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73945 (p : Pattern) (ha : d238915 p = 1) (hb : d287734 p = 1) : d289399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28869 q = 1) (hb : d287734 q = 1) : d40817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28869, d40817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73932 q ha hb
    | true =>
      simp only [d28869, d40817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73930 q ha hb
  have h2 (q : Pattern) (ha : d28870 q = 1) (hb : d287734 q = 1) : d40818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28870, d40818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28870, d40818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28871 q = 1) (hb : d287734 q = 1) : d40819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28871, d40819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28871, d40819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28872 q = 1) (hb : d287734 q = 1) : d40820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28872, d40820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28872, d40820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28876 q = 1) (hb : d287734 q = 1) : d40827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28876, d40827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73933 q ha hb
    | true =>
      simp only [d28876, d40827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73931 q ha hb
  have h6 (q : Pattern) (ha : d28877 q = 1) (hb : d287734 q = 1) : d40828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28877, d40828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28877, d40828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28878 q = 1) (hb : d287734 q = 1) : d40829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28878, d40829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28878, d40829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28919 q = 1) (hb : d287734 q = 1) : d40881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28919, d40881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73943 q ha hb
    | true =>
      simp only [d28919, d40881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73925 q ha hb
  have h9 (q : Pattern) (ha : d238911 q = 1) (hb : d287734 q = 1) : d289395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238911, d289395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238911, d289395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28957 q = 1) (hb : d287734 q = 1) : d40953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28957, d40953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73944 q ha hb
    | true =>
      simp only [d28957, d40953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28958 q = 1) (hb : d287734 q = 1) : d40954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28958, d40954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28958, d40954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238912 q = 1) (hb : d287734 q = 1) : d289396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238912, d289396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238912, d289396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238913 q = 1) (hb : d287734 q = 1) : d289397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238913, d289397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238913, d289397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238914 q = 1) (hb : d287734 q = 1) : d289398 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238914, d289398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238914, d289398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d238915 q = 1) (hb : d287734 q = 1) : d289399 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238915, d289399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238915, d289399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73946 (p : Pattern) (ha : d916 p = 1) (hb : d287734 p = 1) : d40960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d287734 q = 1) : d40790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d287734 q = 1) : d40791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d40791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d40791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d287734 q = 1) : d40815 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d40815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d40815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d287734 q = 1) : d40960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d40960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d40960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73947 (p : Pattern) (ha : d922 p = 1) (hb : d287734 p = 1) : d40966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d287734 q = 1) : d40790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d40790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d287734 q = 1) : d40824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d40824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d40824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d287734 q = 1) : d40825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d40825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d40825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d287734 q = 1) : d40966 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d40966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d40966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73948 (p : Pattern) (ha : d28963 p = 1) (hb : d287734 p = 1) : d40959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d287734 q = 1) : d40780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73924 q ha hb
    | true =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d287734 q = 1) : d40781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d287734 q = 1) : d40786 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28846 q = 1) (hb : d287734 q = 1) : d40787 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28846, d40787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28846, d40787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28867 q = 1) (hb : d287734 q = 1) : d40813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28867, d40813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28867, d40813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28963 q = 1) (hb : d287734 q = 1) : d40959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28963, d40959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28963, d40959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73949 (p : Pattern) (ha : d28968 p = 1) (hb : d287734 p = 1) : d40965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d287734 q = 1) : d40780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73924 q ha hb
    | true =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d287734 q = 1) : d40781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d287734 q = 1) : d40784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73913 q ha hb
    | true =>
      simp only [d774, d40784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d287734 q = 1) : d40785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d40785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28845 q = 1) (hb : d287734 q = 1) : d40786 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28845, d40786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28873 q = 1) (hb : d287734 q = 1) : d40821 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28873, d40821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28873, d40821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28874 q = 1) (hb : d287734 q = 1) : d40822 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28874, d40822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28874, d40822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28968 q = 1) (hb : d287734 q = 1) : d40965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28968, d40965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28968, d40965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73950 (p : Pattern) (ha : d28972 p = 1) (hb : d287734 p = 1) : d40970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28913 q = 1) (hb : d287734 q = 1) : d40875 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28913, d40875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73942 q ha hb
    | true =>
      simp only [d28913, d40875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28914 q = 1) (hb : d287734 q = 1) : d40876 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28914, d40876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28914, d40876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28843 q = 1) (hb : d287734 q = 1) : d40780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73924 q ha hb
    | true =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28844 q = 1) (hb : d287734 q = 1) : d40781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28915 q = 1) (hb : d287734 q = 1) : d40877 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28915, d40877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28915, d40877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28916 q = 1) (hb : d287734 q = 1) : d40878 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28916, d40878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28916, d40878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28917 q = 1) (hb : d287734 q = 1) : d40879 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28917, d40879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28917, d40879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28972 q = 1) (hb : d287734 q = 1) : d40970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28972, d40970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28972, d40970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73951 (p : Pattern) (ha : d28977 p = 1) (hb : d287734 p = 1) : d40976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28843 q = 1) (hb : d287734 q = 1) : d40780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73924 q ha hb
    | true =>
      simp only [d28843, d40780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28844 q = 1) (hb : d287734 q = 1) : d40781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28844, d40781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28953 q = 1) (hb : d287734 q = 1) : d40949 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d28953, d40949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28953, d40949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28954 q = 1) (hb : d287734 q = 1) : d40950 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d28954, d40950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28954, d40950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28955 q = 1) (hb : d287734 q = 1) : d40951 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d28955, d40951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28955, d40951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28977 q = 1) (hb : d287734 q = 1) : d40976 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d28977, d40976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28977, d40976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73952 (p : Pattern) (ha : d238920 p = 1) (hb : d287734 p = 1) : d289404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28869 q = 1) (hb : d287734 q = 1) : d40817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28869, d40817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73932 q ha hb
    | true =>
      simp only [d28869, d40817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73930 q ha hb
  have h2 (q : Pattern) (ha : d28870 q = 1) (hb : d287734 q = 1) : d40818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28870, d40818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28870, d40818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d28871 q = 1) (hb : d287734 q = 1) : d40819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28871, d40819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28871, d40819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28872 q = 1) (hb : d287734 q = 1) : d40820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28872, d40820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28872, d40820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28876 q = 1) (hb : d287734 q = 1) : d40827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28876, d40827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73933 q ha hb
    | true =>
      simp only [d28876, d40827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73931 q ha hb
  have h6 (q : Pattern) (ha : d28877 q = 1) (hb : d287734 q = 1) : d40828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28877, d40828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28877, d40828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28878 q = 1) (hb : d287734 q = 1) : d40829 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28878, d40829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28878, d40829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28919 q = 1) (hb : d287734 q = 1) : d40881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28919, d40881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73943 q ha hb
    | true =>
      simp only [d28919, d40881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73925 q ha hb
  have h9 (q : Pattern) (ha : d238911 q = 1) (hb : d287734 q = 1) : d289395 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238911, d289395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238911, d289395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28957 q = 1) (hb : d287734 q = 1) : d40953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28957, d40953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73944 q ha hb
    | true =>
      simp only [d28957, d40953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28958 q = 1) (hb : d287734 q = 1) : d40954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28958, d40954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d28958, d40954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d238912 q = 1) (hb : d287734 q = 1) : d289396 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238912, d289396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238912, d289396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238913 q = 1) (hb : d287734 q = 1) : d289397 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238913, d289397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238913, d289397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238914 q = 1) (hb : d287734 q = 1) : d289398 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238914, d289398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238914, d289398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d28964 q = 1) (hb : d287734 q = 1) : d40961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28964, d40961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73948 q ha hb
    | true =>
      simp only [d28964, d40961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73946 q ha hb
  have h16 (q : Pattern) (ha : d28965 q = 1) (hb : d287734 q = 1) : d40962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28965, d40962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28965, d40962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28966 q = 1) (hb : d287734 q = 1) : d40963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28966, d40963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28966, d40963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d28967 q = 1) (hb : d287734 q = 1) : d40964 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d28967, d40964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28967, d40964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d28969 q = 1) (hb : d287734 q = 1) : d40967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28969, d40967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73949 q ha hb
    | true =>
      simp only [d28969, d40967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73947 q ha hb
  have h20 (q : Pattern) (ha : d28970 q = 1) (hb : d287734 q = 1) : d40968 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28970, d40968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28970, d40968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d28971 q = 1) (hb : d287734 q = 1) : d40969 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d28971, d40969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d28971, d40969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d28973 q = 1) (hb : d287734 q = 1) : d40971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28973, d40971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73950 q ha hb
    | true =>
      simp only [d28973, d40971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73927 q ha hb
  have h23 (q : Pattern) (ha : d238916 q = 1) (hb : d287734 q = 1) : d289400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238916, d289400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d238916, d289400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d28978 q = 1) (hb : d287734 q = 1) : d40977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28978, d40977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73951 q ha hb
    | true =>
      simp only [d28978, d40977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d28979 q = 1) (hb : d287734 q = 1) : d40978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28979, d40978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d28979, d40978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d238917 q = 1) (hb : d287734 q = 1) : d289401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238917, d289401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d238917, d289401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d238918 q = 1) (hb : d287734 q = 1) : d289402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238918, d289402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238918, d289402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d238919 q = 1) (hb : d287734 q = 1) : d289403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238919, d289403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d238919, d289403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d238920 q = 1) (hb : d287734 q = 1) : d289404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238920, d289404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238920, d289404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro73953 (p : Pattern) (ha : d238927 p = 1) (hb : d287734 p = 1) : d289411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28973 q = 1) (hb : d287734 q = 1) : d40971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28973, d40971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73950 q ha hb
    | true =>
      simp only [d28973, d40971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73927 q ha hb
  have h2 (q : Pattern) (ha : d238916 q = 1) (hb : d287734 q = 1) : d289400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238916, d289400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238916, d289400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28978 q = 1) (hb : d287734 q = 1) : d40977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d28978, d40977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73951 q ha hb
    | true =>
      simp only [d28978, d40977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d28979 q = 1) (hb : d287734 q = 1) : d40978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d28979, d40978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28979, d40978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238917 q = 1) (hb : d287734 q = 1) : d289401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238917, d289401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238917, d289401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238925 q = 1) (hb : d287734 q = 1) : d289409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238925, d289409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238925, d289409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238926 q = 1) (hb : d287734 q = 1) : d289410 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238926, d289410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238926, d289410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238927 q = 1) (hb : d287734 q = 1) : d289411 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238927, d289411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238927, d289411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73954 (p : Pattern) (ha : d29007 p = 1) (hb : d287734 p = 1) : d41024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28998 q = 1) (hb : d287734 q = 1) : d41010 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28998, d41010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28998, d41010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73938 q ha hb
  have h2 (q : Pattern) (ha : d28892 q = 1) (hb : d287734 q = 1) : d40846 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28892, d40846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73938 q ha hb
    | true =>
      simp only [d28892, d40846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28999 q = 1) (hb : d287734 q = 1) : d41011 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28999, d41011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28999, d41011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28893 q = 1) (hb : d287734 q = 1) : d40847 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28893, d40847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28893, d40847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29000 q = 1) (hb : d287734 q = 1) : d41012 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29000, d41012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29000, d41012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29001 q = 1) (hb : d287734 q = 1) : d41013 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29001, d41013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29001, d41013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29002 q = 1) (hb : d287734 q = 1) : d41014 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29002, d41014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29002, d41014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73939 q ha hb
  have h8 (q : Pattern) (ha : d28897 q = 1) (hb : d287734 q = 1) : d40851 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28897, d40851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73939 q ha hb
    | true =>
      simp only [d28897, d40851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29003 q = 1) (hb : d287734 q = 1) : d41015 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29003, d41015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29003, d41015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28898 q = 1) (hb : d287734 q = 1) : d40852 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28898, d40852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28898, d40852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29004 q = 1) (hb : d287734 q = 1) : d41016 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29004, d41016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29004, d41016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d29005 q = 1) (hb : d287734 q = 1) : d41017 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29005, d41017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29005, d41017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29006 q = 1) (hb : d287734 q = 1) : d41018 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29006, d41018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29006, d41018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23534 q = 1) (hb : d287734 q = 1) : d41019 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23534, d41019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23534, d41019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73934 q ha hb
  have h15 (q : Pattern) (ha : d23422 q = 1) (hb : d287734 q = 1) : d40859 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d40859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73934 q ha hb
    | true =>
      simp only [d23422, d40859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23535 q = 1) (hb : d287734 q = 1) : d41020 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23535, d41020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23535, d41020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23423 q = 1) (hb : d287734 q = 1) : d40860 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d40860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23423, d40860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23536 q = 1) (hb : d287734 q = 1) : d41021 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23536, d41021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23536, d41021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23537 q = 1) (hb : d287734 q = 1) : d41022 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23537, d41022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23537, d41022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d23310 q = 1) (hb : d287734 q = 1) : d40655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d40655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d40655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
  have h21 (q : Pattern) (ha : d23231 q = 1) (hb : d287734 q = 1) : d40517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
    | true =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d23311 q = 1) (hb : d287734 q = 1) : d40656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d40656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d23311, d40656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d23232 q = 1) (hb : d287734 q = 1) : d40518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d23312 q = 1) (hb : d287734 q = 1) : d40657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d40657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d23312, d40657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d23313 q = 1) (hb : d287734 q = 1) : d40658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d40658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d23313, d40658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d23538 q = 1) (hb : d287734 q = 1) : d41023 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23538, d41023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d23538, d41023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d29007 q = 1) (hb : d287734 q = 1) : d41024 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29007, d41024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29007, d41024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro73955 (p : Pattern) (ha : d29009 p = 1) (hb : d287734 p = 1) : d41030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28794 q = 1) (hb : d287734 q = 1) : d40646 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28794, d40646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28794, d40646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73886 q ha hb
  have h2 (q : Pattern) (ha : d28746 q = 1) (hb : d287734 q = 1) : d40504 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73886 q ha hb
    | true =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28795 q = 1) (hb : d287734 q = 1) : d40647 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28795, d40647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28795, d40647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28747 q = 1) (hb : d287734 q = 1) : d40505 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28796 q = 1) (hb : d287734 q = 1) : d40648 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28796, d40648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28796, d40648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28797 q = 1) (hb : d287734 q = 1) : d40649 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28797, d40649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28797, d40649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28798 q = 1) (hb : d287734 q = 1) : d40650 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28798, d40650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28798, d40650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73887 q ha hb
  have h8 (q : Pattern) (ha : d28751 q = 1) (hb : d287734 q = 1) : d40509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28751, d40509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73887 q ha hb
    | true =>
      simp only [d28751, d40509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28799 q = 1) (hb : d287734 q = 1) : d40651 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28799, d40651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28799, d40651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28752 q = 1) (hb : d287734 q = 1) : d40510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28752, d40510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28752, d40510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d28800 q = 1) (hb : d287734 q = 1) : d40652 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28800, d40652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28800, d40652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28801 q = 1) (hb : d287734 q = 1) : d40653 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28801, d40653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d28801, d40653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28802 q = 1) (hb : d287734 q = 1) : d40654 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28802, d40654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28802, d40654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d23310 q = 1) (hb : d287734 q = 1) : d40655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d40655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d40655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
  have h15 (q : Pattern) (ha : d23231 q = 1) (hb : d287734 q = 1) : d40517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
    | true =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23311 q = 1) (hb : d287734 q = 1) : d40656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d40656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23311, d40656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23232 q = 1) (hb : d287734 q = 1) : d40518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23312 q = 1) (hb : d287734 q = 1) : d40657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d40657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23312, d40657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d23313 q = 1) (hb : d287734 q = 1) : d40658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d40658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d23313, d40658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d971 q = 1) (hb : d287734 q = 1) : d41025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d41025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d41025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
  have h21 (q : Pattern) (ha : d751 q = 1) (hb : d287734 q = 1) : d40760 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
    | true =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d972 q = 1) (hb : d287734 q = 1) : d41026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d41026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d972, d41026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d752 q = 1) (hb : d287734 q = 1) : d40761 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d973 q = 1) (hb : d287734 q = 1) : d41027 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d41027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d973, d41027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d974 q = 1) (hb : d287734 q = 1) : d41028 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d41028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d974, d41028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d29008 q = 1) (hb : d287734 q = 1) : d41029 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29008, d41029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d29008, d41029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d29009 q = 1) (hb : d287734 q = 1) : d41030 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29009, d41030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29009, d41030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro73956 (p : Pattern) (ha : d29013 p = 1) (hb : d287734 p = 1) : d41035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23310 q = 1) (hb : d287734 q = 1) : d40655 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23310, d40655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23310, d40655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
  have h2 (q : Pattern) (ha : d23231 q = 1) (hb : d287734 q = 1) : d40517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73883 q ha hb
    | true =>
      simp only [d23231, d40517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23311 q = 1) (hb : d287734 q = 1) : d40656 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23311, d40656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23311, d40656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23232 q = 1) (hb : d287734 q = 1) : d40518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23232, d40518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23312 q = 1) (hb : d287734 q = 1) : d40657 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23312, d40657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23312, d40657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d23313 q = 1) (hb : d287734 q = 1) : d40658 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23313, d40658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23313, d40658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d287734 q = 1) : d41025 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d41025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d41025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d287734 q = 1) : d40760 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73910 q ha hb
    | true =>
      simp only [d751, d40760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d287734 q = 1) : d41026 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d41026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d41026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d287734 q = 1) : d40761 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d40761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d287734 q = 1) : d41027 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d41027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d41027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d287734 q = 1) : d41028 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d41028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d41028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29008 q = 1) (hb : d287734 q = 1) : d41029 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29008, d41029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29008, d41029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d287734 q = 1) : d41034 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d41034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d41034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29013 q = 1) (hb : d287734 q = 1) : d41035 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29013, d41035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29013, d41035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73957 (p : Pattern) (ha : d29023 p = 1) (hb : d287734 p = 1) : d41051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29010 q = 1) (hb : d287734 q = 1) : d41031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29010, d41031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73954 q ha hb
    | true =>
      simp only [d29010, d41031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73955 q ha hb
  have h2 (q : Pattern) (ha : d29011 q = 1) (hb : d287734 q = 1) : d41032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29011, d41032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29011, d41032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29012 q = 1) (hb : d287734 q = 1) : d41033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29012, d41033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29012, d41033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29014 q = 1) (hb : d287734 q = 1) : d41036 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29014, d41036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73955 q ha hb
    | true =>
      simp only [d29014, d41036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73956 q ha hb
  have h5 (q : Pattern) (ha : d29015 q = 1) (hb : d287734 q = 1) : d41037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29015, d41037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29015, d41037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29016 q = 1) (hb : d287734 q = 1) : d41038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29016, d41038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29016, d41038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29017 q = 1) (hb : d287734 q = 1) : d41039 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29017, d41039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29017, d41039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29018 q = 1) (hb : d287734 q = 1) : d41042 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29018, d41042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73955 q ha hb
    | true =>
      simp only [d29018, d41042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73918 q ha hb
  have h9 (q : Pattern) (ha : d29019 q = 1) (hb : d287734 q = 1) : d41043 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29019, d41043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29019, d41043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29020 q = 1) (hb : d287734 q = 1) : d41044 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29020, d41044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29020, d41044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d987 q = 1) (hb : d287734 q = 1) : d41046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d41046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73918 q ha hb
    | true =>
      simp only [d987, d41046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73919 q ha hb
  have h12 (q : Pattern) (ha : d988 q = 1) (hb : d287734 q = 1) : d41047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d41047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d41047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d989 q = 1) (hb : d287734 q = 1) : d41048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d41048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d41048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29021 q = 1) (hb : d287734 q = 1) : d41049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29021, d41049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29021, d41049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29022 q = 1) (hb : d287734 q = 1) : d41050 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29022, d41050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29022, d41050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29023 q = 1) (hb : d287734 q = 1) : d41051 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29023, d41051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29023, d41051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro73958 (p : Pattern) (ha : d29027 p = 1) (hb : d287734 p = 1) : d41056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29018 q = 1) (hb : d287734 q = 1) : d41042 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29018, d41042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73955 q ha hb
    | true =>
      simp only [d29018, d41042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73918 q ha hb
  have h2 (q : Pattern) (ha : d29019 q = 1) (hb : d287734 q = 1) : d41043 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29019, d41043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29019, d41043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29020 q = 1) (hb : d287734 q = 1) : d41044 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29020, d41044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29020, d41044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d287734 q = 1) : d41046 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d41046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73918 q ha hb
    | true =>
      simp only [d987, d41046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73919 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d287734 q = 1) : d41047 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d41047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d41047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d287734 q = 1) : d41048 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d41048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d41048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29021 q = 1) (hb : d287734 q = 1) : d41049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29021, d41049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29021, d41049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d287734 q = 1) : d41054 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d41054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d41054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29026 q = 1) (hb : d287734 q = 1) : d41055 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29026, d41055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29026, d41055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29027 q = 1) (hb : d287734 q = 1) : d41056 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29027, d41056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29027, d41056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro73959 (p : Pattern) (ha : d29033 p = 1) (hb : d287734 p = 1) : d41062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29024 q = 1) (hb : d287734 q = 1) : d41052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29024, d41052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73957 q ha hb
    | true =>
      simp only [d29024, d41052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29025 q = 1) (hb : d287734 q = 1) : d41053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29025, d41053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29025, d41053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29028 q = 1) (hb : d287734 q = 1) : d41057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29028, d41057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73958 q ha hb
    | true =>
      simp only [d29028, d41057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29029 q = 1) (hb : d287734 q = 1) : d41058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29029, d41058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29029, d41058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29030 q = 1) (hb : d287734 q = 1) : d41059 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29030, d41059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29030, d41059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29031 q = 1) (hb : d287734 q = 1) : d41060 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29031, d41060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29031, d41060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29032 q = 1) (hb : d287734 q = 1) : d41061 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29032, d41061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29032, d41061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29033 q = 1) (hb : d287734 q = 1) : d41062 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29033, d41062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29033, d41062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73960 (p : Pattern) (ha : d29037 p = 1) (hb : d287734 p = 1) : d41070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29028 q = 1) (hb : d287734 q = 1) : d41057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29028, d41057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73958 q ha hb
    | true =>
      simp only [d29028, d41057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29029 q = 1) (hb : d287734 q = 1) : d41058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29029, d41058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29029, d41058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d287734 q = 1) : d41065 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d41065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73920 q ha hb
    | true =>
      simp only [d1006, d41065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d287734 q = 1) : d41066 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d41066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d41066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29034 q = 1) (hb : d287734 q = 1) : d41067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29034, d41067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29034, d41067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29035 q = 1) (hb : d287734 q = 1) : d41068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29035, d41068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29035, d41068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29036 q = 1) (hb : d287734 q = 1) : d41069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29036, d41069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29036, d41069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29037 q = 1) (hb : d287734 q = 1) : d41070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29037, d41070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29037, d41070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73961 (p : Pattern) (ha : d29067 p = 1) (hb : d287734 p = 1) : d41124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29028 q = 1) (hb : d287734 q = 1) : d41057 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29028, d41057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73958 q ha hb
    | true =>
      simp only [d29028, d41057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29029 q = 1) (hb : d287734 q = 1) : d41058 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29029, d41058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29029, d41058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29064 q = 1) (hb : d287734 q = 1) : d41121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29064, d41121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29064, d41121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29065 q = 1) (hb : d287734 q = 1) : d41122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29065, d41122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29065, d41122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29066 q = 1) (hb : d287734 q = 1) : d41123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29066, d41123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29066, d41123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29067 q = 1) (hb : d287734 q = 1) : d41124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29067, d41124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29067, d41124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73962 (p : Pattern) (ha : d238937 p = 1) (hb : d287734 p = 1) : d289421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29038 q = 1) (hb : d287734 q = 1) : d41071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29038, d41071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73959 q ha hb
    | true =>
      simp only [d29038, d41071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73960 q ha hb
  have h2 (q : Pattern) (ha : d238933 q = 1) (hb : d287734 q = 1) : d289417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238933, d289417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238933, d289417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29068 q = 1) (hb : d287734 q = 1) : d41125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29068, d41125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73961 q ha hb
    | true =>
      simp only [d29068, d41125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29069 q = 1) (hb : d287734 q = 1) : d41126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29069, d41126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29069, d41126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d238934 q = 1) (hb : d287734 q = 1) : d289418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238934, d289418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d238934, d289418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238935 q = 1) (hb : d287734 q = 1) : d289419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238935, d289419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238935, d289419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238936 q = 1) (hb : d287734 q = 1) : d289420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238936, d289420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238936, d289420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238937 q = 1) (hb : d287734 q = 1) : d289421 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238937, d289421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238937, d289421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73963 (p : Pattern) (ha : d238943 p = 1) (hb : d287734 p = 1) : d289427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28855 q = 1) (hb : d287734 q = 1) : d40800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28855, d40800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28855, d40800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73926 q ha hb
  have h2 (q : Pattern) (ha : d28856 q = 1) (hb : d287734 q = 1) : d40801 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28856, d40801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28856, d40801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28864 q = 1) (hb : d287734 q = 1) : d40810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28864, d40810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73926 q ha hb
    | true =>
      simp only [d28864, d40810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73928 q ha hb
  have h4 (q : Pattern) (ha : d28865 q = 1) (hb : d287734 q = 1) : d40811 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d28865, d40811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28865, d40811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28866 q = 1) (hb : d287734 q = 1) : d40812 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d28866, d40812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28866, d40812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238921 q = 1) (hb : d287734 q = 1) : d289405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238921, d289405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73945 q ha hb
    | true =>
      simp only [d238921, d289405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73952 q ha hb
  have h7 (q : Pattern) (ha : d28986 q = 1) (hb : d287734 q = 1) : d40996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d28986, d40996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73929 q ha hb
    | true =>
      simp only [d28986, d40996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73916 q ha hb
  have h8 (q : Pattern) (ha : d238922 q = 1) (hb : d287734 q = 1) : d289406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238922, d289406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238922, d289406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238923 q = 1) (hb : d287734 q = 1) : d289407 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238923, d289407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d238923, d289407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d238924 q = 1) (hb : d287734 q = 1) : d289408 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238924, d289408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238924, d289408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d238928 q = 1) (hb : d287734 q = 1) : d289412 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238928, d289412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238928, d289412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73953 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d287734 q = 1) : d41005 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d41005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d41005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73917 q ha hb
  have h13 (q : Pattern) (ha : d238929 q = 1) (hb : d287734 q = 1) : d289413 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238929, d289413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d238929, d289413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d238930 q = 1) (hb : d287734 q = 1) : d289414 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238930, d289414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238930, d289414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d238931 q = 1) (hb : d287734 q = 1) : d289415 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238931, d289415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d238931, d289415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d238932 q = 1) (hb : d287734 q = 1) : d289416 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238932, d289416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238932, d289416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d238938 q = 1) (hb : d287734 q = 1) : d289422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238938, d289422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238938, d289422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73962 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d287734 q = 1) : d41142 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d41142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d41142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73922 q ha hb
  have h19 (q : Pattern) (ha : d238939 q = 1) (hb : d287734 q = 1) : d289423 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238939, d289423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238939, d289423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d238940 q = 1) (hb : d287734 q = 1) : d289424 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238940, d289424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d238940, d289424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d238941 q = 1) (hb : d287734 q = 1) : d289425 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238941, d289425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d238941, d289425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d238942 q = 1) (hb : d287734 q = 1) : d289426 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238942, d289426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d238942, d289426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d238943 q = 1) (hb : d287734 q = 1) : d289427 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238943, d289427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238943, d289427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro73964 (p : Pattern) (ha : d238949 p = 1) (hb : d287734 p = 1) : d289433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238944 q = 1) (hb : d287734 q = 1) : d289428 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238944, d289428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238944, d289428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73963 q ha hb
  have h2 (q : Pattern) (ha : d238945 q = 1) (hb : d287734 q = 1) : d289429 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238945, d289429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238945, d289429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238946 q = 1) (hb : d287734 q = 1) : d289430 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238946, d289430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238946, d289430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238947 q = 1) (hb : d287734 q = 1) : d289431 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238947, d289431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238947, d289431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238948 q = 1) (hb : d287734 q = 1) : d289432 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238948, d289432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238948, d289432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238949 q = 1) (hb : d287734 q = 1) : d289433 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238949, d289433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238949, d289433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73965 (p : Pattern) (ha : d29093 p = 1) (hb : d287734 p = 1) : d289438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d287734 q = 1) : d40267 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9796 q = 1) (hb : d287734 q = 1) : d41175 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d41175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9796, d41175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d29088 q = 1) (hb : d287734 q = 1) : d289436 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29088, d289436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29088, d289436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d29089 q = 1) (hb : d287734 q = 1) : d289437 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29089, d289437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29089, d289437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d29092 q = 1) (hb : d287734 q = 1) : d29092 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d29093 q = 1) (hb : d287734 q = 1) : d289438 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29093, d289438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29093, d289438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73966 (p : Pattern) (ha : d29099 p = 1) (hb : d287734 p = 1) : d289444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28892 q = 1) (hb : d287734 q = 1) : d40846 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28892, d40846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73938 q ha hb
    | true =>
      simp only [d28892, d40846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28893 q = 1) (hb : d287734 q = 1) : d40847 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28893, d40847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28893, d40847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28894 q = 1) (hb : d287734 q = 1) : d40848 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28894, d40848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28894, d40848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28895 q = 1) (hb : d287734 q = 1) : d40849 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28895, d40849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28895, d40849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28897 q = 1) (hb : d287734 q = 1) : d40851 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28897, d40851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73939 q ha hb
    | true =>
      simp only [d28897, d40851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d28898 q = 1) (hb : d287734 q = 1) : d40852 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28898, d40852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28898, d40852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d28899 q = 1) (hb : d287734 q = 1) : d40853 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28899, d40853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28899, d40853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28900 q = 1) (hb : d287734 q = 1) : d40854 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28900, d40854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28900, d40854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d28901 q = 1) (hb : d287734 q = 1) : d40855 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d28901, d40855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28901, d40855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23422 q = 1) (hb : d287734 q = 1) : d40859 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d40859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73934 q ha hb
    | true =>
      simp only [d23422, d40859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23423 q = 1) (hb : d287734 q = 1) : d40860 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d40860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23423, d40860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23424 q = 1) (hb : d287734 q = 1) : d40861 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d40861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d40861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23425 q = 1) (hb : d287734 q = 1) : d40862 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d40862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23425, d40862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29094 q = 1) (hb : d287734 q = 1) : d289439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73965 q ha hb
    | true =>
      simp only [d29094, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29095 q = 1) (hb : d287734 q = 1) : d289440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d29095, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d29096 q = 1) (hb : d287734 q = 1) : d289441 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29096, d289441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29096, d289441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d29097 q = 1) (hb : d287734 q = 1) : d289442 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29097, d289442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d29097, d289442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d29098 q = 1) (hb : d287734 q = 1) : d289443 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29098, d289443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29098, d289443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29099 q = 1) (hb : d287734 q = 1) : d289444 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29099, d289444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29099, d289444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73967 (p : Pattern) (ha : d29100 p = 1) (hb : d287734 p = 1) : d289445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d287734 q = 1) : d40152 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73823 q ha hb
    | true =>
      simp only [d133, d287734, d40152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d287734 q = 1) : d40153 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d40153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d287734 q = 1) : d40267 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d40267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d287734 q = 1) : d20 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d287734 q = 1) : d40154 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d40154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d287734 q = 1) : d40268 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d40268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d40268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d317 q = 1) (hb : d287734 q = 1) : d40269 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d40269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d40269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d29092 q = 1) (hb : d287734 q = 1) : d29092 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d29100 q = 1) (hb : d287734 q = 1) : d289445 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29100, d289445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29100, d289445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro73968 (p : Pattern) (ha : d29107 p = 1) (hb : d287734 p = 1) : d289452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28746 q = 1) (hb : d287734 q = 1) : d40504 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73886 q ha hb
    | true =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d28747 q = 1) (hb : d287734 q = 1) : d40505 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28748 q = 1) (hb : d287734 q = 1) : d40506 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28748, d40506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28748, d40506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28749 q = 1) (hb : d287734 q = 1) : d40507 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28749, d40507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28749, d40507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29101 q = 1) (hb : d287734 q = 1) : d289446 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73967 q ha hb
    | true =>
      simp only [d29101, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29102 q = 1) (hb : d287734 q = 1) : d289447 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29102, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29103 q = 1) (hb : d287734 q = 1) : d289448 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29103, d289448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29103, d289448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29104 q = 1) (hb : d287734 q = 1) : d289449 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29104, d289449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29104, d289449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29105 q = 1) (hb : d287734 q = 1) : d289450 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29105, d289450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29105, d289450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29094 q = 1) (hb : d287734 q = 1) : d289439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73965 q ha hb
    | true =>
      simp only [d29094, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29095 q = 1) (hb : d287734 q = 1) : d289440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29095, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29096 q = 1) (hb : d287734 q = 1) : d289441 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29096, d289441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29096, d289441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29097 q = 1) (hb : d287734 q = 1) : d289442 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29097, d289442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29097, d289442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d29106 q = 1) (hb : d287734 q = 1) : d289451 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29106, d289451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29106, d289451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d29107 q = 1) (hb : d287734 q = 1) : d289452 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29107, d289452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29107, d289452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro73969 (p : Pattern) (ha : d29120 p = 1) (hb : d287734 p = 1) : d289457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29101 q = 1) (hb : d287734 q = 1) : d289446 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73967 q ha hb
    | true =>
      simp only [d29101, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29102 q = 1) (hb : d287734 q = 1) : d289447 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29102, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29103 q = 1) (hb : d287734 q = 1) : d289448 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29103, d289448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29103, d289448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29104 q = 1) (hb : d287734 q = 1) : d289449 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29104, d289449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29104, d289449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29111 q = 1) (hb : d287734 q = 1) : d289456 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29111, d289456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29111, d289456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29119 q = 1) (hb : d287734 q = 1) : d29119 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d29120 q = 1) (hb : d287734 q = 1) : d289457 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29120, d289457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29120, d289457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro73970 (p : Pattern) (ha : d29127 p = 1) (hb : d287734 p = 1) : d289464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29108 q = 1) (hb : d287734 q = 1) : d289453 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29108, d289453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73966 q ha hb
    | true =>
      simp only [d29108, d289453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73968 q ha hb
  have h2 (q : Pattern) (ha : d29109 q = 1) (hb : d287734 q = 1) : d289454 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29109, d289454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29109, d289454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29110 q = 1) (hb : d287734 q = 1) : d289455 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29110, d289455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29110, d289455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29121 q = 1) (hb : d287734 q = 1) : d289458 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73968 q ha hb
    | true =>
      simp only [d29121, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73969 q ha hb
  have h5 (q : Pattern) (ha : d29122 q = 1) (hb : d287734 q = 1) : d289459 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29123 q = 1) (hb : d287734 q = 1) : d289460 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29124 q = 1) (hb : d287734 q = 1) : d289461 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29124, d289461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29124, d289461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29125 q = 1) (hb : d287734 q = 1) : d289462 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29125, d289462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29125, d289462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29126 q = 1) (hb : d287734 q = 1) : d289463 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29126, d289463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29126, d289463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29127 q = 1) (hb : d287734 q = 1) : d289464 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29127, d289464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29127, d289464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro73971 (p : Pattern) (ha : d29131 p = 1) (hb : d287734 p = 1) : d289468 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29121 q = 1) (hb : d287734 q = 1) : d289458 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73968 q ha hb
    | true =>
      simp only [d29121, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73969 q ha hb
  have h2 (q : Pattern) (ha : d29122 q = 1) (hb : d287734 q = 1) : d289459 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29123 q = 1) (hb : d287734 q = 1) : d289460 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29125 q = 1) (hb : d287734 q = 1) : d289462 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29125, d289462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29125, d289462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29130 q = 1) (hb : d287734 q = 1) : d289467 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29130, d289467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29130, d289467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29131 q = 1) (hb : d287734 q = 1) : d289468 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29131, d289468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29131, d289468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73972 (p : Pattern) (ha : d29137 p = 1) (hb : d287734 p = 1) : d289474 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d287734 q = 1) : d289465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73970 q ha hb
    | true =>
      simp only [d29128, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d287734 q = 1) : d289466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d287734 q = 1) : d289469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73971 q ha hb
    | true =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d287734 q = 1) : d289470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d287734 q = 1) : d289471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29135 q = 1) (hb : d287734 q = 1) : d289472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29135, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29135, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29136 q = 1) (hb : d287734 q = 1) : d289473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29136, d289473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29136, d289473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29137 q = 1) (hb : d287734 q = 1) : d289474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29137, d289474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29137, d289474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73973 (p : Pattern) (ha : d29141 p = 1) (hb : d287734 p = 1) : d289478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d287734 q = 1) : d289469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73971 q ha hb
    | true =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d287734 q = 1) : d289470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d287734 q = 1) : d289475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29139 q = 1) (hb : d287734 q = 1) : d289476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29139, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29139, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29140 q = 1) (hb : d287734 q = 1) : d289477 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29140, d289477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29140, d289477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29141 q = 1) (hb : d287734 q = 1) : d289478 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29141, d289478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29141, d289478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73974 (p : Pattern) (ha : d29147 p = 1) (hb : d287734 p = 1) : d289484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29142 q = 1) (hb : d287734 q = 1) : d289479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29142, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73972 q ha hb
    | true =>
      simp only [d29142, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73973 q ha hb
  have h2 (q : Pattern) (ha : d29143 q = 1) (hb : d287734 q = 1) : d289480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29143, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29143, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29144 q = 1) (hb : d287734 q = 1) : d289481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29144, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29144, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29145 q = 1) (hb : d287734 q = 1) : d289482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29145, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29145, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29146 q = 1) (hb : d287734 q = 1) : d289483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29146, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29146, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29147 q = 1) (hb : d287734 q = 1) : d289484 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29147, d289484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29147, d289484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73975 (p : Pattern) (ha : d29150 p = 1) (hb : d287734 p = 1) : d289487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d287734 q = 1) : d289465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73970 q ha hb
    | true =>
      simp only [d29128, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d287734 q = 1) : d289466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d287734 q = 1) : d289469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73971 q ha hb
    | true =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d287734 q = 1) : d289470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d287734 q = 1) : d289471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29135 q = 1) (hb : d287734 q = 1) : d289472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29135, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29135, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29136 q = 1) (hb : d287734 q = 1) : d289473 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29136, d289473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29136, d289473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29150 q = 1) (hb : d287734 q = 1) : d289487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29150, d289487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29150, d289487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro73976 (p : Pattern) (ha : d29151 p = 1) (hb : d287734 p = 1) : d289488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d287734 q = 1) : d289469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73971 q ha hb
    | true =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d287734 q = 1) : d289470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d287734 q = 1) : d289475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29139 q = 1) (hb : d287734 q = 1) : d289476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29139, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29139, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29140 q = 1) (hb : d287734 q = 1) : d289477 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29140, d289477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29140, d289477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29151 q = 1) (hb : d287734 q = 1) : d289488 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29151, d289488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29151, d289488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73977 (p : Pattern) (ha : d29157 p = 1) (hb : d287734 p = 1) : d289494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29142 q = 1) (hb : d287734 q = 1) : d289479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29142, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73972 q ha hb
    | true =>
      simp only [d29142, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73973 q ha hb
  have h2 (q : Pattern) (ha : d29143 q = 1) (hb : d287734 q = 1) : d289480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29143, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29143, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29144 q = 1) (hb : d287734 q = 1) : d289481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29144, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29144, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29145 q = 1) (hb : d287734 q = 1) : d289482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29145, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29145, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29146 q = 1) (hb : d287734 q = 1) : d289483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29146, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29146, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29152 q = 1) (hb : d287734 q = 1) : d289489 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29152, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73975 q ha hb
    | true =>
      simp only [d29152, d289489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73976 q ha hb
  have h7 (q : Pattern) (ha : d29153 q = 1) (hb : d287734 q = 1) : d289490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29153, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29153, d289490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29154 q = 1) (hb : d287734 q = 1) : d289491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29154, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29154, d289491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29155 q = 1) (hb : d287734 q = 1) : d289492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29155, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29155, d289492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29156 q = 1) (hb : d287734 q = 1) : d289493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29156, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29156, d289493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29157 q = 1) (hb : d287734 q = 1) : d289494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29157, d289494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29157, d289494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73978 (p : Pattern) (ha : d29339 p = 1) (hb : d287734 p = 1) : d289579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29142 q = 1) (hb : d287734 q = 1) : d289479 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29142, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73972 q ha hb
    | true =>
      simp only [d29142, d289479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73973 q ha hb
  have h2 (q : Pattern) (ha : d29143 q = 1) (hb : d287734 q = 1) : d289480 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29143, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29143, d289480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29144 q = 1) (hb : d287734 q = 1) : d289481 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29144, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29144, d289481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29145 q = 1) (hb : d287734 q = 1) : d289482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29145, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29145, d289482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29146 q = 1) (hb : d287734 q = 1) : d289483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29146, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29146, d289483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29334 q = 1) (hb : d287734 q = 1) : d289574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29334, d289574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73973 q ha hb
    | true =>
      simp only [d29334, d289574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29335 q = 1) (hb : d287734 q = 1) : d289575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29335, d289575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29335, d289575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29336 q = 1) (hb : d287734 q = 1) : d289576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29336, d289576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29336, d289576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29337 q = 1) (hb : d287734 q = 1) : d289577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29337, d289577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29337, d289577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29338 q = 1) (hb : d287734 q = 1) : d289578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29338, d289578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29338, d289578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29339 q = 1) (hb : d287734 q = 1) : d289579 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29339, d289579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29339, d289579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73979 (p : Pattern) (ha : d29345 p = 1) (hb : d287734 p = 1) : d289585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29334 q = 1) (hb : d287734 q = 1) : d289574 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29334, d289574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73973 q ha hb
    | true =>
      simp only [d29334, d289574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29335 q = 1) (hb : d287734 q = 1) : d289575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29335, d289575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29335, d289575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29336 q = 1) (hb : d287734 q = 1) : d289576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29336, d289576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29336, d289576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29337 q = 1) (hb : d287734 q = 1) : d289577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29337, d289577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29337, d289577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29338 q = 1) (hb : d287734 q = 1) : d289578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29338, d289578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29338, d289578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29340 q = 1) (hb : d287734 q = 1) : d289580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29340, d289580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73976 q ha hb
    | true =>
      simp only [d29340, d289580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29341 q = 1) (hb : d287734 q = 1) : d289581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29341, d289581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29341, d289581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29342 q = 1) (hb : d287734 q = 1) : d289582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29342, d289582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29342, d289582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29343 q = 1) (hb : d287734 q = 1) : d289583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29343, d289583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29343, d289583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29344 q = 1) (hb : d287734 q = 1) : d289584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29344, d289584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29344, d289584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29345 q = 1) (hb : d287734 q = 1) : d289585 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29345, d289585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29345, d289585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73980 (p : Pattern) (ha : d29354 p = 1) (hb : d287734 p = 1) : d289594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29340 q = 1) (hb : d287734 q = 1) : d289580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29340, d289580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73976 q ha hb
    | true =>
      simp only [d29340, d289580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29341 q = 1) (hb : d287734 q = 1) : d289581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29341, d289581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29341, d289581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29342 q = 1) (hb : d287734 q = 1) : d289582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29342, d289582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29342, d289582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29343 q = 1) (hb : d287734 q = 1) : d289583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29343, d289583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29343, d289583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29344 q = 1) (hb : d287734 q = 1) : d289584 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29344, d289584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29344, d289584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29354 q = 1) (hb : d287734 q = 1) : d289594 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29354, d289594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29354, d289594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73981 (p : Pattern) (ha : d29390 p = 1) (hb : d287734 p = 1) : d289620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d28794 q = 1) (hb : d287734 q = 1) : d40646 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28794, d40646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d28794, d40646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73886 q ha hb
  have h2 (q : Pattern) (ha : d28746 q = 1) (hb : d287734 q = 1) : d40504 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73886 q ha hb
    | true =>
      simp only [d28746, d40504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d28795 q = 1) (hb : d287734 q = 1) : d40647 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28795, d40647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d28795, d40647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28747 q = 1) (hb : d287734 q = 1) : d40505 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d28747, d40505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28796 q = 1) (hb : d287734 q = 1) : d40648 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d28796, d40648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28796, d40648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d28797 q = 1) (hb : d287734 q = 1) : d40649 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28797, d40649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d28797, d40649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29385 q = 1) (hb : d287734 q = 1) : d289615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29385, d289615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29385, d289615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73967 q ha hb
  have h8 (q : Pattern) (ha : d29101 q = 1) (hb : d287734 q = 1) : d289446 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73967 q ha hb
    | true =>
      simp only [d29101, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29386 q = 1) (hb : d287734 q = 1) : d289616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29386, d289616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29386, d289616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29102 q = 1) (hb : d287734 q = 1) : d289447 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29102, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29387 q = 1) (hb : d287734 q = 1) : d289617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29387, d289617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29387, d289617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d29388 q = 1) (hb : d287734 q = 1) : d289618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29388, d289618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29388, d289618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d29389 q = 1) (hb : d287734 q = 1) : d289619 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29389, d289619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29389, d289619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29370 q = 1) (hb : d287734 q = 1) : d289600 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29370, d289600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29370, d289600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73965 q ha hb
  have h15 (q : Pattern) (ha : d29094 q = 1) (hb : d287734 q = 1) : d289439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73965 q ha hb
    | true =>
      simp only [d29094, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d29371 q = 1) (hb : d287734 q = 1) : d289601 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29371, d289601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d29371, d289601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d29095 q = 1) (hb : d287734 q = 1) : d289440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29095, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d29372 q = 1) (hb : d287734 q = 1) : d289602 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29372, d289602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d29372, d289602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29373 q = 1) (hb : d287734 q = 1) : d289603 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29373, d289603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d29373, d289603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d29379 q = 1) (hb : d287734 q = 1) : d289609 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29379, d289609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d29379, d289609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d29390 q = 1) (hb : d287734 q = 1) : d289620 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29390, d289620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29390, d289620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro73982 (p : Pattern) (ha : d29400 p = 1) (hb : d287734 p = 1) : d289625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29385 q = 1) (hb : d287734 q = 1) : d289615 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29385, d289615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29385, d289615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73967 q ha hb
  have h2 (q : Pattern) (ha : d29101 q = 1) (hb : d287734 q = 1) : d289446 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73967 q ha hb
    | true =>
      simp only [d29101, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29386 q = 1) (hb : d287734 q = 1) : d289616 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29386, d289616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29386, d289616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29102 q = 1) (hb : d287734 q = 1) : d289447 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29102, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29387 q = 1) (hb : d287734 q = 1) : d289617 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29387, d289617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29387, d289617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29388 q = 1) (hb : d287734 q = 1) : d289618 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29388, d289618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29388, d289618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29394 q = 1) (hb : d287734 q = 1) : d289624 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29394, d289624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29394, d289624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29399 q = 1) (hb : d287734 q = 1) : d29399 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d29400 q = 1) (hb : d287734 q = 1) : d289625 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29400, d289625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29400, d289625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro73983 (p : Pattern) (ha : d29419 p = 1) (hb : d287734 p = 1) : d289644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29401 q = 1) (hb : d287734 q = 1) : d289626 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29401, d289626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73981 q ha hb
    | true =>
      simp only [d29401, d289626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73982 q ha hb
  have h2 (q : Pattern) (ha : d29402 q = 1) (hb : d287734 q = 1) : d289627 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29402, d289627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29402, d289627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29403 q = 1) (hb : d287734 q = 1) : d289628 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29403, d289628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29403, d289628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29409 q = 1) (hb : d287734 q = 1) : d289634 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29409, d289634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29409, d289634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29418 q = 1) (hb : d287734 q = 1) : d289643 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29418, d289643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29418, d289643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29419 q = 1) (hb : d287734 q = 1) : d289644 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29419, d289644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29419, d289644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73984 (p : Pattern) (ha : d29505 p = 1) (hb : d287734 p = 1) : d289676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29420 q = 1) (hb : d287734 q = 1) : d289645 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29420, d289645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73983 q ha hb
    | true =>
      simp only [d29420, d289645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29421 q = 1) (hb : d287734 q = 1) : d289646 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29421, d289646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29421, d289646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29502 q = 1) (hb : d287734 q = 1) : d289673 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29502, d289673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29502, d289673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29503 q = 1) (hb : d287734 q = 1) : d289674 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29503, d289674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29503, d289674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29504 q = 1) (hb : d287734 q = 1) : d289675 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29504, d289675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29504, d289675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29505 q = 1) (hb : d287734 q = 1) : d289676 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29505, d289676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29505, d289676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73985 (p : Pattern) (ha : d29511 p = 1) (hb : d287734 p = 1) : d289682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29506 q = 1) (hb : d287734 q = 1) : d289677 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d29506, d289677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73984 q ha hb
    | true =>
      simp only [d29506, d289677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29507 q = 1) (hb : d287734 q = 1) : d289678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d29507, d289678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29507, d289678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29508 q = 1) (hb : d287734 q = 1) : d289679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d29508, d289679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29508, d289679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29509 q = 1) (hb : d287734 q = 1) : d289680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d29509, d289680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29509, d289680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29510 q = 1) (hb : d287734 q = 1) : d289681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d29510, d289681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29510, d289681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29511 q = 1) (hb : d287734 q = 1) : d289682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d29511, d289682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29511, d289682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73986 (p : Pattern) (ha : d29162 p = 1) (hb : d287734 p = 1) : d289499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d287734 q = 1) : d289465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73970 q ha hb
    | true =>
      simp only [d29128, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d287734 q = 1) : d289466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d287734 q = 1) : d289469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73971 q ha hb
    | true =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d287734 q = 1) : d289470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d287734 q = 1) : d289471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29135 q = 1) (hb : d287734 q = 1) : d289472 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29135, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29135, d289472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29161 q = 1) (hb : d287734 q = 1) : d289498 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29161, d289498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29161, d289498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29162 q = 1) (hb : d287734 q = 1) : d289499 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29162, d289499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29162, d289499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73987 (p : Pattern) (ha : d29164 p = 1) (hb : d287734 p = 1) : d289501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d287734 q = 1) : d289469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73971 q ha hb
    | true =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d287734 q = 1) : d289470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d287734 q = 1) : d289475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29139 q = 1) (hb : d287734 q = 1) : d289476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29139, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29139, d289476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29163 q = 1) (hb : d287734 q = 1) : d289500 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29163, d289500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29163, d289500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29164 q = 1) (hb : d287734 q = 1) : d289501 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29164, d289501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29164, d289501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73988 (p : Pattern) (ha : d29171 p = 1) (hb : d287734 p = 1) : d289508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29128 q = 1) (hb : d287734 q = 1) : d289465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73970 q ha hb
    | true =>
      simp only [d29128, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29129 q = 1) (hb : d287734 q = 1) : d289466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29132 q = 1) (hb : d287734 q = 1) : d289469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73971 q ha hb
    | true =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29133 q = 1) (hb : d287734 q = 1) : d289470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29134 q = 1) (hb : d287734 q = 1) : d289471 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29134, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29134, d289471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29169 q = 1) (hb : d287734 q = 1) : d289506 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29169, d289506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29169, d289506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29170 q = 1) (hb : d287734 q = 1) : d289507 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29170, d289507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29170, d289507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29171 q = 1) (hb : d287734 q = 1) : d289508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29171, d289508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29171, d289508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73989 (p : Pattern) (ha : d29174 p = 1) (hb : d287734 p = 1) : d289511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29132 q = 1) (hb : d287734 q = 1) : d289469 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73971 q ha hb
    | true =>
      simp only [d29132, d289469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29133 q = 1) (hb : d287734 q = 1) : d289470 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29133, d289470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29138 q = 1) (hb : d287734 q = 1) : d289475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29138, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29138, d289475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29172 q = 1) (hb : d287734 q = 1) : d289509 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29172, d289509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29172, d289509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29173 q = 1) (hb : d287734 q = 1) : d289510 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29173, d289510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29173, d289510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29174 q = 1) (hb : d287734 q = 1) : d289511 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29174, d289511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29174, d289511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73990 (p : Pattern) (ha : d23694 p = 1) (hb : d287734 p = 1) : d41284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d287734 q = 1) : d40831 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d287734, d40831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73935 q ha hb
    | true =>
      simp only [d822, d287734, d40831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d287734 q = 1) : d40832 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d40832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d40832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d531 q = 1) (hb : d287734 q = 1) : d40493 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73884 q ha hb
    | true =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d532 q = 1) (hb : d287734 q = 1) : d40494 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d824 q = 1) (hb : d287734 q = 1) : d40833 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d40833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d824, d40833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d23692 q = 1) (hb : d287734 q = 1) : d41282 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23692, d41282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d23692, d41282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d23693 q = 1) (hb : d287734 q = 1) : d41283 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23693, d41283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23693, d41283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d533 q = 1) (hb : d287734 q = 1) : d40495 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d23419 q = 1) (hb : d287734 q = 1) : d40856 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d40856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d23419, d40856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d23420 q = 1) (hb : d287734 q = 1) : d40857 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d40857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23420, d40857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d23694 q = 1) (hb : d287734 q = 1) : d41284 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d23694, d41284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d23694, d41284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro73991 (p : Pattern) (ha : d1199 p = 1) (hb : d253269 p = 1) : d2000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d253269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d307 q = 1) : d307 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309 q = 1) (hb : d253269 q = 1) : d1997 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309, d253269, d1997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d528 q = 1) (hb : d253269 q = 1) : d1998 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d1998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d820 q = 1) (hb : d253269 q = 1) : d1999 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d820, d1999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d820, d1999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1199 q = 1) (hb : d253269 q = 1) : d2000 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1199, d2000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1199, d2000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro73992 (p : Pattern) (ha : d29181 p = 1) (hb : d287734 p = 1) : d41271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1200 q = 1) (hb : d287734 q = 1) : d30077 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d287734, d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73991 q ha hb
    | true =>
      simp only [d1200, d287734, d30077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1201 q = 1) (hb : d287734 q = 1) : d30078 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1201, d30078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d822 q = 1) (hb : d287734 q = 1) : d40831 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d287734, d40831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73935 q ha hb
    | true =>
      simp only [d822, d287734, d40831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d823 q = 1) (hb : d287734 q = 1) : d40832 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d40832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d823, d40832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d1202 q = 1) (hb : d287734 q = 1) : d41265 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1202, d41265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1202, d41265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d24014 q = 1) (hb : d287734 q = 1) : d41266 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d24014, d41266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d24014, d41266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d24015 q = 1) (hb : d287734 q = 1) : d41267 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d24015, d41267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d24015, d41267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d531 q = 1) (hb : d287734 q = 1) : d40493 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73884 q ha hb
    | true =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d532 q = 1) (hb : d287734 q = 1) : d40494 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d824 q = 1) (hb : d287734 q = 1) : d40833 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d40833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d824, d40833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28883 q = 1) (hb : d287734 q = 1) : d40837 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28883, d287734, d40837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73937 q ha hb
    | true =>
      simp only [d28883, d287734, d40837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d28884 q = 1) (hb : d287734 q = 1) : d40838 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28884, d40838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28884, d40838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d29178 q = 1) (hb : d287734 q = 1) : d41268 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d29178, d41268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29178, d41268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29179 q = 1) (hb : d287734 q = 1) : d41269 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d29179, d41269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d29179, d41269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29180 q = 1) (hb : d287734 q = 1) : d41270 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d29180, d41270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29180, d41270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d29181 q = 1) (hb : d287734 q = 1) : d41271 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29181, d41271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29181, d41271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro73993 (p : Pattern) (ha : d29186 p = 1) (hb : d287734 p = 1) : d41276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d287734 q = 1) : d40831 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d287734, d40831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73935 q ha hb
    | true =>
      simp only [d822, d287734, d40831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d287734 q = 1) : d40832 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d40832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d40832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d531 q = 1) (hb : d287734 q = 1) : d40493 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73884 q ha hb
    | true =>
      simp only [d531, d287734, d40493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d532 q = 1) (hb : d287734 q = 1) : d40494 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d532, d40494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d824 q = 1) (hb : d287734 q = 1) : d40833 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d40833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d824, d40833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d28880 q = 1) (hb : d287734 q = 1) : d32702 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28880, d287734, d32702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73936 q ha hb
    | true =>
      simp only [d28880, d287734, d32702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d28881 q = 1) (hb : d287734 q = 1) : d32703 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28881, d32703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28881, d32703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d28883 q = 1) (hb : d287734 q = 1) : d40837 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d28883, d287734, d40837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73937 q ha hb
    | true =>
      simp only [d28883, d287734, d40837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d28884 q = 1) (hb : d287734 q = 1) : d40838 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d28884, d40838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28884, d40838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d28885 q = 1) (hb : d287734 q = 1) : d40839 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d28885, d40839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d28885, d40839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d28886 q = 1) (hb : d287734 q = 1) : d40840 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d28886, d40840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d28886, d40840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d28887 q = 1) (hb : d287734 q = 1) : d40841 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d28887, d40841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d28887, d40841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d313 q = 1) (hb : d287734 q = 1) : d40265 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73843 q ha hb
    | true =>
      simp only [d313, d287734, d40265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d314 q = 1) (hb : d287734 q = 1) : d40266 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d314, d40266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d533 q = 1) (hb : d287734 q = 1) : d40495 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d533, d40495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23419 q = 1) (hb : d287734 q = 1) : d40856 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d23419, d40856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23419, d40856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d23420 q = 1) (hb : d287734 q = 1) : d40857 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23420, d40857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d23420, d40857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d29186 q = 1) (hb : d287734 q = 1) : d41276 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d29186, d41276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d29186, d41276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73994 (p : Pattern) (ha : d29192 p = 1) (hb : d287734 p = 1) : d41290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29182 q = 1) (hb : d287734 q = 1) : d41272 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29182, d41272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73992 q ha hb
    | true =>
      simp only [d29182, d41272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29183 q = 1) (hb : d287734 q = 1) : d41273 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29183, d41273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29183, d41273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29184 q = 1) (hb : d287734 q = 1) : d41274 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29184, d41274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29184, d41274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29185 q = 1) (hb : d287734 q = 1) : d41275 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29185, d41275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29185, d41275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29187 q = 1) (hb : d287734 q = 1) : d41277 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29187, d41277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73993 q ha hb
    | true =>
      simp only [d29187, d41277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29188 q = 1) (hb : d287734 q = 1) : d41278 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29188, d41278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29188, d41278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29189 q = 1) (hb : d287734 q = 1) : d41279 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29189, d41279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29189, d41279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29190 q = 1) (hb : d287734 q = 1) : d41280 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29190, d41280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29190, d41280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29191 q = 1) (hb : d287734 q = 1) : d41281 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29191, d41281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29191, d41281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23695 q = 1) (hb : d287734 q = 1) : d41285 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23695, d41285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73990 q ha hb
    | true =>
      simp only [d23695, d41285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23696 q = 1) (hb : d287734 q = 1) : d41286 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23696, d41286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23696, d41286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23697 q = 1) (hb : d287734 q = 1) : d41287 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23697, d41287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23697, d41287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23698 q = 1) (hb : d287734 q = 1) : d41288 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23698, d41288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23698, d41288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d23422 q = 1) (hb : d287734 q = 1) : d40859 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d40859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73934 q ha hb
    | true =>
      simp only [d23422, d40859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d23423 q = 1) (hb : d287734 q = 1) : d40860 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d40860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d23423, d40860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d23424 q = 1) (hb : d287734 q = 1) : d40861 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d40861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d40861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d23425 q = 1) (hb : d287734 q = 1) : d40862 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d40862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d23425, d40862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d23699 q = 1) (hb : d287734 q = 1) : d41289 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d23699, d41289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d23699, d41289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d29192 q = 1) (hb : d287734 q = 1) : d41290 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29192, d41290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29192, d41290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro73995 (p : Pattern) (ha : d29196 p = 1) (hb : d287734 p = 1) : d289518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23422 q = 1) (hb : d287734 q = 1) : d40859 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d23422, d40859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73934 q ha hb
    | true =>
      simp only [d23422, d40859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23423 q = 1) (hb : d287734 q = 1) : d40860 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d23423, d40860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d23423, d40860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d23424 q = 1) (hb : d287734 q = 1) : d40861 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d23424, d40861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23424, d40861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d23425 q = 1) (hb : d287734 q = 1) : d40862 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d23425, d40862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23425, d40862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29094 q = 1) (hb : d287734 q = 1) : d289439 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29094, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73965 q ha hb
    | true =>
      simp only [d29094, d289439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29095 q = 1) (hb : d287734 q = 1) : d289440 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29095, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29095, d289440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29096 q = 1) (hb : d287734 q = 1) : d289441 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29096, d289441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29096, d289441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29097 q = 1) (hb : d287734 q = 1) : d289442 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29097, d289442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29097, d289442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d29098 q = 1) (hb : d287734 q = 1) : d289443 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29098, d289443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29098, d289443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29106 q = 1) (hb : d287734 q = 1) : d289451 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29106, d289451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29106, d289451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29196 q = 1) (hb : d287734 q = 1) : d289518 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29196, d289518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d29196, d289518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro73996 (p : Pattern) (ha : d29202 p = 1) (hb : d287734 p = 1) : d289524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29193 q = 1) (hb : d287734 q = 1) : d289515 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29193, d289515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73994 q ha hb
    | true =>
      simp only [d29193, d289515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73966 q ha hb
  have h2 (q : Pattern) (ha : d29194 q = 1) (hb : d287734 q = 1) : d289516 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29194, d289516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29194, d289516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29195 q = 1) (hb : d287734 q = 1) : d289517 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29195, d289517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29195, d289517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29197 q = 1) (hb : d287734 q = 1) : d289519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29197, d289519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73966 q ha hb
    | true =>
      simp only [d29197, d289519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73995 q ha hb
  have h5 (q : Pattern) (ha : d29198 q = 1) (hb : d287734 q = 1) : d289520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29198, d289520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29198, d289520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29199 q = 1) (hb : d287734 q = 1) : d289521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29199, d289521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29199, d289521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29200 q = 1) (hb : d287734 q = 1) : d289522 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29200, d289522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29200, d289522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29108 q = 1) (hb : d287734 q = 1) : d289453 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29108, d289453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73966 q ha hb
    | true =>
      simp only [d29108, d289453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73968 q ha hb
  have h9 (q : Pattern) (ha : d29109 q = 1) (hb : d287734 q = 1) : d289454 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29109, d289454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29109, d289454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29110 q = 1) (hb : d287734 q = 1) : d289455 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29110, d289455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29110, d289455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29121 q = 1) (hb : d287734 q = 1) : d289458 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73968 q ha hb
    | true =>
      simp only [d29121, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73969 q ha hb
  have h12 (q : Pattern) (ha : d29122 q = 1) (hb : d287734 q = 1) : d289459 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29123 q = 1) (hb : d287734 q = 1) : d289460 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d29124 q = 1) (hb : d287734 q = 1) : d289461 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29124, d289461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29124, d289461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d29201 q = 1) (hb : d287734 q = 1) : d289523 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29201, d289523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29201, d289523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d29202 q = 1) (hb : d287734 q = 1) : d289524 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29202, d289524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d29202, d289524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro73997 (p : Pattern) (ha : d29208 p = 1) (hb : d287734 p = 1) : d289530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29203 q = 1) (hb : d287734 q = 1) : d289525 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29203, d289525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73996 q ha hb
    | true =>
      simp only [d29203, d289525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29204 q = 1) (hb : d287734 q = 1) : d289526 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29204, d289526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29204, d289526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29128 q = 1) (hb : d287734 q = 1) : d289465 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d29128, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73970 q ha hb
    | true =>
      simp only [d29128, d289465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d29129 q = 1) (hb : d287734 q = 1) : d289466 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d29129, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29129, d289466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d29205 q = 1) (hb : d287734 q = 1) : d289527 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d29205, d289527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d29205, d289527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29206 q = 1) (hb : d287734 q = 1) : d289528 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d29206, d289528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29206, d289528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d29207 q = 1) (hb : d287734 q = 1) : d289529 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d29207, d289529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d29207, d289529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d29208 q = 1) (hb : d287734 q = 1) : d289530 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d29208, d289530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29208, d289530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro73998 (p : Pattern) (ha : d29290 p = 1) (hb : d287734 p = 1) : d289533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29101 q = 1) (hb : d287734 q = 1) : d289446 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d29101, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73967 q ha hb
    | true =>
      simp only [d29101, d289446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d29102 q = 1) (hb : d287734 q = 1) : d289447 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d29102, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d29102, d289447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d29103 q = 1) (hb : d287734 q = 1) : d289448 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d29103, d289448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29103, d289448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29104 q = 1) (hb : d287734 q = 1) : d289449 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d29104, d289449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29104, d289449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29111 q = 1) (hb : d287734 q = 1) : d289456 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29111, d289456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29111, d289456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d29290 q = 1) (hb : d287734 q = 1) : d289533 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d29290, d289533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29290, d289533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro73999 (p : Pattern) (ha : d29296 p = 1) (hb : d287734 p = 1) : d289539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d287734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29108 q = 1) (hb : d287734 q = 1) : d289453 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29108, d289453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73966 q ha hb
    | true =>
      simp only [d29108, d289453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73968 q ha hb
  have h2 (q : Pattern) (ha : d29109 q = 1) (hb : d287734 q = 1) : d289454 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29109, d289454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29109, d289454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d29110 q = 1) (hb : d287734 q = 1) : d289455 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29110, d289455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29110, d289455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d29121 q = 1) (hb : d287734 q = 1) : d289458 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29121, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73968 q ha hb
    | true =>
      simp only [d29121, d289458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73969 q ha hb
  have h5 (q : Pattern) (ha : d29122 q = 1) (hb : d287734 q = 1) : d289459 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29122, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29122, d289459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d29123 q = 1) (hb : d287734 q = 1) : d289460 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29123, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29123, d289460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29124 q = 1) (hb : d287734 q = 1) : d289461 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29124, d289461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d29124, d289461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d29291 q = 1) (hb : d287734 q = 1) : d289534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d29291, d289534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73968 q ha hb
    | true =>
      simp only [d29291, d289534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73998 q ha hb
  have h9 (q : Pattern) (ha : d29292 q = 1) (hb : d287734 q = 1) : d289535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d29292, d289535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29292, d289535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d29293 q = 1) (hb : d287734 q = 1) : d289536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d29293, d289536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d29293, d289536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d29294 q = 1) (hb : d287734 q = 1) : d289537 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d29294, d289537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29294, d289537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d29295 q = 1) (hb : d287734 q = 1) : d289538 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d29295, d289538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d29295, d289538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d29296 q = 1) (hb : d287734 q = 1) : d289539 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d29296, d289539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d29296, d289539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
end NetHack.Soko22Hazard87
