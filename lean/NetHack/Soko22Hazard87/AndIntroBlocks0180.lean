import NetHack.Soko22Hazard87.AndIntroBlocks0179
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro45000 (p : Pattern) (ha : d20606 p = 1) (hb : d102052 p = 1) : d20011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20569 q = 1) (hb : d102052 q = 1) : d19966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20569, d19966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44999 q ha hb
    | true =>
      simp only [d20569, d19966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20570 q = 1) (hb : d102052 q = 1) : d19967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20570, d19967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20570, d19967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20603 q = 1) (hb : d102052 q = 1) : d20008 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20603, d20008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20603, d20008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20604 q = 1) (hb : d102052 q = 1) : d20009 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20604, d20009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20604, d20009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20605 q = 1) (hb : d102052 q = 1) : d20010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20605, d20010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20605, d20010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20606 q = 1) (hb : d102052 q = 1) : d20011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20606, d20011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20606, d20011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45001 (p : Pattern) (ha : d20612 p = 1) (hb : d102052 p = 1) : d20017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20607 q = 1) (hb : d102052 q = 1) : d20012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20607, d20012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45000 q ha hb
    | true =>
      simp only [d20607, d20012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20608 q = 1) (hb : d102052 q = 1) : d20013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20608, d20013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20608, d20013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20609 q = 1) (hb : d102052 q = 1) : d20014 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20609, d20014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20609, d20014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20610 q = 1) (hb : d102052 q = 1) : d20015 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20610, d20015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20610, d20015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20611 q = 1) (hb : d102052 q = 1) : d20016 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20611, d20016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20611, d20016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20612 q = 1) (hb : d102052 q = 1) : d20017 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20612, d20017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20612, d20017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45002 (p : Pattern) (ha : d16362 p = 1) (hb : d102052 p = 1) : d9603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d965 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d834 q = 1) (hb : d102052 q = 1) : d834 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d966 q = 1) (hb : d102052 q = 1) : d9576 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d9576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d966, d9576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d835 q = 1) (hb : d102052 q = 1) : d835 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d967 q = 1) (hb : d102052 q = 1) : d9577 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d9577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d967, d9577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d968 q = 1) (hb : d102052 q = 1) : d9578 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d9578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d968, d9578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9586 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16356 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16356, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9587 q = 1) (hb : d102052 q = 1) : d9587 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d16357 q = 1) (hb : d102052 q = 1) : d9588 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d9588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16357, d9588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9589 q = 1) (hb : d102052 q = 1) : d9589 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d16358 q = 1) (hb : d102052 q = 1) : d9590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16358, d9590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16358, d9590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16359 q = 1) (hb : d102052 q = 1) : d9591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16359, d9591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16359, d9591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d16360 q = 1) (hb : d102052 q = 1) : d9592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16360, d9592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16360, d9592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d9596 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d14644 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14644, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d9597 q = 1) (hb : d102052 q = 1) : d9597 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d14645 q = 1) (hb : d102052 q = 1) : d9598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d9598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14645, d9598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9599 q = 1) (hb : d102052 q = 1) : d9599 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d14646 q = 1) (hb : d102052 q = 1) : d9600 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14646, d9600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14646, d9600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d14647 q = 1) (hb : d102052 q = 1) : d9601 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14647, d9601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d14647, d9601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d9467 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d12858 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d9468 q = 1) (hb : d102052 q = 1) : d9468 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d12859 q = 1) (hb : d102052 q = 1) : d9469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d12859, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d9470 q = 1) (hb : d102052 q = 1) : d9470 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d12860 q = 1) (hb : d102052 q = 1) : d9471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d9471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d12860, d9471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d12861 q = 1) (hb : d102052 q = 1) : d9472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d9472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d12861, d9472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h31 (q : Pattern) (ha : d16361 q = 1) (hb : d102052 q = 1) : d9602 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16361, d9602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d16361, d9602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d16362 q = 1) (hb : d102052 q = 1) : d9603 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16362, d9603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16362, d9603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  exact h32 p ha hb
theorem andIntro45003 (p : Pattern) (ha : d16363 p = 1) (hb : d102052 p = 1) : d9608 p = 1 := by
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
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d750 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d971 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d751 q = 1) (hb : d102052 q = 1) : d751 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d972 q = 1) (hb : d102052 q = 1) : d9604 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d972, d9604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d752 q = 1) (hb : d102052 q = 1) : d752 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d973 q = 1) (hb : d102052 q = 1) : d9605 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d9605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d973, d9605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d974 q = 1) (hb : d102052 q = 1) : d9606 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d9606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d974, d9606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h31 (q : Pattern) (ha : d12862 q = 1) (hb : d102052 q = 1) : d9607 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d9607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d12862, d9607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d16363 q = 1) (hb : d102052 q = 1) : d9608 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16363, d9608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16363, d9608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  exact h32 p ha hb
theorem andIntro45004 (p : Pattern) (ha : d16367 p = 1) (hb : d102052 p = 1) : d9613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12858 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d9468 q = 1) (hb : d102052 q = 1) : d9468 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12859 q = 1) (hb : d102052 q = 1) : d9469 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12859, d9469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9470 q = 1) (hb : d102052 q = 1) : d9470 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12860 q = 1) (hb : d102052 q = 1) : d9471 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d9471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12860, d9471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12861 q = 1) (hb : d102052 q = 1) : d9472 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d9472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12861, d9472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h16 (q : Pattern) (ha : d12862 q = 1) (hb : d102052 q = 1) : d9607 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d9607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12862, d9607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h18 (q : Pattern) (ha : d16367 q = 1) (hb : d102052 q = 1) : d9613 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16367, d9613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16367, d9613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45005 (p : Pattern) (ha : d20558 p = 1) (hb : d102052 p = 1) : d19952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16364 q = 1) (hb : d102052 q = 1) : d9609 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d9609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45002 q ha hb
    | true =>
      simp only [d16364, d9609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45003 q ha hb
  have h2 (q : Pattern) (ha : d16365 q = 1) (hb : d102052 q = 1) : d19941 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d19941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16365, d19941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16366 q = 1) (hb : d102052 q = 1) : d19942 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d19942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, d19942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16368 q = 1) (hb : d102052 q = 1) : d9614 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d9614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45003 q ha hb
    | true =>
      simp only [d16368, d9614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45004 q ha hb
  have h5 (q : Pattern) (ha : d16369 q = 1) (hb : d102052 q = 1) : d19943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d19943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16369, d19943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16370 q = 1) (hb : d102052 q = 1) : d19944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d19944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, d19944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16371 q = 1) (hb : d102052 q = 1) : d19945 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d19945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16371, d19945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16372 q = 1) (hb : d102052 q = 1) : d9620 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d9620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45003 q ha hb
    | true =>
      simp only [d16372, d9620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44997 q ha hb
  have h9 (q : Pattern) (ha : d16373 q = 1) (hb : d102052 q = 1) : d19946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d19946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d19946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16374 q = 1) (hb : d102052 q = 1) : d19947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d19947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d19947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d987 q = 1) (hb : d102052 q = 1) : d9624 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44997 q ha hb
    | true =>
      simp only [d987, d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44998 q ha hb
  have h12 (q : Pattern) (ha : d988 q = 1) (hb : d102052 q = 1) : d19948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d989 q = 1) (hb : d102052 q = 1) : d19949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16375 q = 1) (hb : d102052 q = 1) : d19950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d19950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16375, d19950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16376 q = 1) (hb : d102052 q = 1) : d19951 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d19951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16376, d19951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9628 q = 1) (hb : d102052 q = 1) : d9628 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d20558 q = 1) (hb : d102052 q = 1) : d19952 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20558, d19952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20558, d19952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45006 (p : Pattern) (ha : d20561 p = 1) (hb : d102052 p = 1) : d19957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16372 q = 1) (hb : d102052 q = 1) : d9620 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d9620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45003 q ha hb
    | true =>
      simp only [d16372, d9620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44997 q ha hb
  have h2 (q : Pattern) (ha : d16373 q = 1) (hb : d102052 q = 1) : d19946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d19946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d19946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16374 q = 1) (hb : d102052 q = 1) : d19947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d19947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d19947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d102052 q = 1) : d9624 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44997 q ha hb
    | true =>
      simp only [d987, d9624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44998 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d102052 q = 1) : d19948 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d19948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d102052 q = 1) : d19949 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d19949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16375 q = 1) (hb : d102052 q = 1) : d19950 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d19950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16375, d19950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d102052 q = 1) : d19955 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d19955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d19955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16380 q = 1) (hb : d102052 q = 1) : d19956 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d19956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16380, d19956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9633 q = 1) (hb : d102052 q = 1) : d9633 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d20561 q = 1) (hb : d102052 q = 1) : d19957 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20561, d19957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20561, d19957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45007 (p : Pattern) (ha : d20567 p = 1) (hb : d102052 p = 1) : d19963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20559 q = 1) (hb : d102052 q = 1) : d19953 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20559, d19953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45005 q ha hb
    | true =>
      simp only [d20559, d19953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20560 q = 1) (hb : d102052 q = 1) : d19954 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20560, d19954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20560, d19954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20562 q = 1) (hb : d102052 q = 1) : d19958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d19958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45006 q ha hb
    | true =>
      simp only [d20562, d19958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20563 q = 1) (hb : d102052 q = 1) : d19959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d19959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, d19959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20564 q = 1) (hb : d102052 q = 1) : d19960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20564, d19960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20564, d19960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20565 q = 1) (hb : d102052 q = 1) : d19961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20565, d19961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20565, d19961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20566 q = 1) (hb : d102052 q = 1) : d19962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20566, d19962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20566, d19962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20567 q = 1) (hb : d102052 q = 1) : d19963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20567, d19963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20567, d19963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45008 (p : Pattern) (ha : d20574 p = 1) (hb : d102052 p = 1) : d19971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20562 q = 1) (hb : d102052 q = 1) : d19958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d19958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45006 q ha hb
    | true =>
      simp only [d20562, d19958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20563 q = 1) (hb : d102052 q = 1) : d19959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d19959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, d19959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20569 q = 1) (hb : d102052 q = 1) : d19966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20569, d19966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44999 q ha hb
    | true =>
      simp only [d20569, d19966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20570 q = 1) (hb : d102052 q = 1) : d19967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20570, d19967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20570, d19967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20571 q = 1) (hb : d102052 q = 1) : d19968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20571, d19968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20571, d19968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20572 q = 1) (hb : d102052 q = 1) : d19969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20572, d19969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20572, d19969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20573 q = 1) (hb : d102052 q = 1) : d19970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20573, d19970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20573, d19970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20574 q = 1) (hb : d102052 q = 1) : d19971 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20574, d19971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20574, d19971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45009 (p : Pattern) (ha : d20595 p = 1) (hb : d102052 p = 1) : d20000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20562 q = 1) (hb : d102052 q = 1) : d19958 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d19958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45006 q ha hb
    | true =>
      simp only [d20562, d19958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20563 q = 1) (hb : d102052 q = 1) : d19959 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d19959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20563, d19959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20592 q = 1) (hb : d102052 q = 1) : d19997 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20592, d19997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20592, d19997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20593 q = 1) (hb : d102052 q = 1) : d19998 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20593, d19998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20593, d19998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20594 q = 1) (hb : d102052 q = 1) : d19999 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20594, d19999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20594, d19999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20595 q = 1) (hb : d102052 q = 1) : d20000 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20595, d20000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20595, d20000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45010 (p : Pattern) (ha : d102052 p = 1) (hb : d130975 p = 1) : d130266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20575 q = 1) (hb : d102052 q = 1) : d19972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20575, d19972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45007 q ha hb
    | true =>
      simp only [d20575, d19972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45008 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d130971 q = 1) : d130262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130971, d130262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130971, d130262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20596 q = 1) (hb : d102052 q = 1) : d20001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20596, d20001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45009 q ha hb
    | true =>
      simp only [d20596, d20001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20597 q = 1) (hb : d102052 q = 1) : d20002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20597, d20002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20597, d20002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130972 q = 1) : d130263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130972, d130263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130972, d130263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130973 q = 1) : d130264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130973, d130264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130973, d130264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d130974 q = 1) : d130265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130974, d130265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130974, d130265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d130975 q = 1) : d130266 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130975, d130266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130975, d130266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45011 (p : Pattern) (ha : d102052 p = 1) (hb : d130981 p = 1) : d130272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d130976 q = 1) : d130267 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130976, d130267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130976, d130267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45010 q ha hb
  have h2 (q : Pattern) (ha : d20613 q = 1) (hb : d102052 q = 1) : d20018 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20613, d20018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20613, d20018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45001 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d130977 q = 1) : d130268 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130977, d130268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130977, d130268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d130978 q = 1) : d130269 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130978, d130269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130978, d130269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130979 q = 1) : d130270 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130979, d130270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130979, d130270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130980 q = 1) : d130271 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130980, d130271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130980, d130271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d130981 q = 1) : d130272 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130981, d130272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130981, d130272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45012 (p : Pattern) (ha : d102052 p = 1) (hb : d130987 p = 1) : d130278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d130982 q = 1) : d130273 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130982, d130273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130982, d130273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45011 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d130983 q = 1) : d130274 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130983, d130274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130983, d130274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d130984 q = 1) : d130275 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130984, d130275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130984, d130275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d130985 q = 1) : d130276 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130985, d130276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130985, d130276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130986 q = 1) : d130277 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130986, d130277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130986, d130277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130987 q = 1) : d130278 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130987, d130278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130987, d130278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45013 (p : Pattern) (ha : d15042 p = 1) (hb : d102052 p = 1) : d9869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1391 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1121 q = 1) (hb : d102052 q = 1) : d1121 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1392 q = 1) (hb : d102052 q = 1) : d9829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1392, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d102052 q = 1) : d1122 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1393 q = 1) (hb : d102052 q = 1) : d9830 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1393, d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1394 q = 1) (hb : d102052 q = 1) : d9831 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1394, d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1400 q = 1) (hb : d102052 q = 1) : d9868 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d9868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1400, d9868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d9843 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15019 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d9844 q = 1) (hb : d102052 q = 1) : d9844 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15020 q = 1) (hb : d102052 q = 1) : d9845 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15020, d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9846 q = 1) (hb : d102052 q = 1) : d9846 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15021 q = 1) (hb : d102052 q = 1) : d9847 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d9847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15021, d9847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15022 q = 1) (hb : d102052 q = 1) : d9848 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d9848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15022, d9848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d15023 q = 1) (hb : d102052 q = 1) : d9849 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d9849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15023, d9849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d15042 q = 1) (hb : d102052 q = 1) : d9869 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15042, d9869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15042, d9869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45014 (p : Pattern) (ha : d16672 p = 1) (hb : d102052 p = 1) : d9833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1385 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1110 q = 1) (hb : d102052 q = 1) : d1110 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1386 q = 1) (hb : d102052 q = 1) : d9826 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d9826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1386, d9826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1111 q = 1) (hb : d102052 q = 1) : d1111 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1387 q = 1) (hb : d102052 q = 1) : d9827 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d9827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1387, d9827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1388 q = 1) (hb : d102052 q = 1) : d9828 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d9828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1388, d9828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1120 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1391 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1121 q = 1) (hb : d102052 q = 1) : d1121 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d1392 q = 1) (hb : d102052 q = 1) : d9829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1392, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1122 q = 1) (hb : d102052 q = 1) : d1122 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1393 q = 1) (hb : d102052 q = 1) : d9830 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d1393, d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1394 q = 1) (hb : d102052 q = 1) : d9831 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1394, d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d1395 q = 1) (hb : d102052 q = 1) : d9832 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d9832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1395, d9832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d9799 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d15004 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d9800 q = 1) (hb : d102052 q = 1) : d9800 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15005 q = 1) (hb : d102052 q = 1) : d9801 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15005, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9802 q = 1) (hb : d102052 q = 1) : d9802 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d15006 q = 1) (hb : d102052 q = 1) : d9803 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15006, d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d15007 q = 1) (hb : d102052 q = 1) : d9804 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15007, d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d15008 q = 1) (hb : d102052 q = 1) : d9820 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d9820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d15008, d9820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h25 (q : Pattern) (ha : d16672 q = 1) (hb : d102052 q = 1) : d9833 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16672, d9833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16672, d9833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro45015 (p : Pattern) (ha : d20637 p = 1) (hb : d102052 p = 1) : d20059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16693 q = 1) (hb : d102052 q = 1) : d9870 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
    | true =>
      simp only [d16693, d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45013 q ha hb
  have h2 (q : Pattern) (ha : d16694 q = 1) (hb : d102052 q = 1) : d20055 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d20055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d20055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16695 q = 1) (hb : d102052 q = 1) : d20056 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d20056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d20056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16696 q = 1) (hb : d102052 q = 1) : d20057 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d20057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16696, d20057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16697 q = 1) (hb : d102052 q = 1) : d20058 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, d20058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16697, d20058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9874 q = 1) (hb : d102052 q = 1) : d9874 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20637 q = 1) (hb : d102052 q = 1) : d20059 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20637, d20059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20637, d20059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45016 (p : Pattern) (ha : d20678 p = 1) (hb : d102052 p = 1) : d20114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20638 q = 1) (hb : d102052 q = 1) : d20060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d20060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45015 q ha hb
    | true =>
      simp only [d20638, d20060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20639 q = 1) (hb : d102052 q = 1) : d20061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d20061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d20061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20675 q = 1) (hb : d102052 q = 1) : d20111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20675, d20111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20675, d20111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20676 q = 1) (hb : d102052 q = 1) : d20112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20676, d20112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20676, d20112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20677 q = 1) (hb : d102052 q = 1) : d20113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20677, d20113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20677, d20113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20678 q = 1) (hb : d102052 q = 1) : d20114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20678, d20114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20678, d20114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45017 (p : Pattern) (ha : d20684 p = 1) (hb : d102052 p = 1) : d20120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20679 q = 1) (hb : d102052 q = 1) : d20115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20679, d20115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45016 q ha hb
    | true =>
      simp only [d20679, d20115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20680 q = 1) (hb : d102052 q = 1) : d20116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20680, d20116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20680, d20116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20681 q = 1) (hb : d102052 q = 1) : d20117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20681, d20117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20681, d20117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20682 q = 1) (hb : d102052 q = 1) : d20118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20682, d20118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20682, d20118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20683 q = 1) (hb : d102052 q = 1) : d20119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20683, d20119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20683, d20119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20684 q = 1) (hb : d102052 q = 1) : d20120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20684, d20120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20684, d20120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45018 (p : Pattern) (ha : d15024 p = 1) (hb : d102052 p = 1) : d9850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6350 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6350, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5018 q = 1) (hb : d102052 q = 1) : d5018 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6351 q = 1) (hb : d102052 q = 1) : d9837 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, d9837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6351, d9837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5019 q = 1) (hb : d102052 q = 1) : d5019 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6352 q = 1) (hb : d102052 q = 1) : d9838 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6352, d9838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6352, d9838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6353 q = 1) (hb : d102052 q = 1) : d9839 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6353, d9839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6353, d9839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6354 q = 1) (hb : d102052 q = 1) : d9840 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d9840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6354, d9840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d9843 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15019 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d9844 q = 1) (hb : d102052 q = 1) : d9844 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15020 q = 1) (hb : d102052 q = 1) : d9845 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15020, d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9846 q = 1) (hb : d102052 q = 1) : d9846 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15021 q = 1) (hb : d102052 q = 1) : d9847 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d9847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15021, d9847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15022 q = 1) (hb : d102052 q = 1) : d9848 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d9848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15022, d9848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d15023 q = 1) (hb : d102052 q = 1) : d9849 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d9849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15023, d9849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d15024 q = 1) (hb : d102052 q = 1) : d9850 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15024, d9850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15024, d9850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45019 (p : Pattern) (ha : d16655 p = 1) (hb : d102052 p = 1) : d9784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1209 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1376 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1210 q = 1) (hb : d102052 q = 1) : d1210 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1377 q = 1) (hb : d102052 q = 1) : d9746 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, d9746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1377, d9746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1211 q = 1) (hb : d102052 q = 1) : d1211 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1378 q = 1) (hb : d102052 q = 1) : d9747 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1378, d9747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1378, d9747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1379 q = 1) (hb : d102052 q = 1) : d9748 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1379, d9748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1379, d9748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9752 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16649 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16649, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9753 q = 1) (hb : d102052 q = 1) : d9753 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d16650 q = 1) (hb : d102052 q = 1) : d9754 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, d9754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16650, d9754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9755 q = 1) (hb : d102052 q = 1) : d9755 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d16651 q = 1) (hb : d102052 q = 1) : d9756 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16651, d9756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16651, d9756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16652 q = 1) (hb : d102052 q = 1) : d9757 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16652, d9757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16652, d9757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d16653 q = 1) (hb : d102052 q = 1) : d9758 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16653, d9758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16653, d9758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d9762 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d14987 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14987, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d9763 q = 1) (hb : d102052 q = 1) : d9763 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d14988 q = 1) (hb : d102052 q = 1) : d9764 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14988, d9764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14988, d9764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9765 q = 1) (hb : d102052 q = 1) : d9765 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d14989 q = 1) (hb : d102052 q = 1) : d9766 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14989, d9766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14989, d9766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d14990 q = 1) (hb : d102052 q = 1) : d9767 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14990, d9767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d14990, d9767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d9777 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d14994 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d9778 q = 1) (hb : d102052 q = 1) : d9778 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d14995 q = 1) (hb : d102052 q = 1) : d9779 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d14995, d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d9780 q = 1) (hb : d102052 q = 1) : d9780 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d14996 q = 1) (hb : d102052 q = 1) : d9781 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d9781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d14996, d9781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d14997 q = 1) (hb : d102052 q = 1) : d9782 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d9782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d14997, d9782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h31 (q : Pattern) (ha : d16654 q = 1) (hb : d102052 q = 1) : d9783 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16654, d9783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d16654, d9783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d16655 q = 1) (hb : d102052 q = 1) : d9784 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16655, d9784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16655, d9784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  exact h32 p ha hb
theorem andIntro45020 (p : Pattern) (ha : d16662 p = 1) (hb : d102052 p = 1) : d9806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1380 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1100 q = 1) (hb : d102052 q = 1) : d1100 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1381 q = 1) (hb : d102052 q = 1) : d9785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d9785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1381, d9785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1101 q = 1) (hb : d102052 q = 1) : d1101 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1382 q = 1) (hb : d102052 q = 1) : d9786 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d9786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1382, d9786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1383 q = 1) (hb : d102052 q = 1) : d9787 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d9787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1383, d9787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9788 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16656 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16656, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9789 q = 1) (hb : d102052 q = 1) : d9789 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d16657 q = 1) (hb : d102052 q = 1) : d9790 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, d9790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16657, d9790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9791 q = 1) (hb : d102052 q = 1) : d9791 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d16658 q = 1) (hb : d102052 q = 1) : d9792 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16658, d9792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16658, d9792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16659 q = 1) (hb : d102052 q = 1) : d9793 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16659, d9793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d16659, d9793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d16660 q = 1) (hb : d102052 q = 1) : d9794 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16660, d9794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16660, d9794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d9777 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d14994 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d9778 q = 1) (hb : d102052 q = 1) : d9778 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d14995 q = 1) (hb : d102052 q = 1) : d9779 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14995, d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9780 q = 1) (hb : d102052 q = 1) : d9780 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d14996 q = 1) (hb : d102052 q = 1) : d9781 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14996, d9781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14996, d9781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d14997 q = 1) (hb : d102052 q = 1) : d9782 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14997, d9782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d14997, d9782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d9799 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d15004 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d9800 q = 1) (hb : d102052 q = 1) : d9800 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d15005 q = 1) (hb : d102052 q = 1) : d9801 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d15005, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d9802 q = 1) (hb : d102052 q = 1) : d9802 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d15006 q = 1) (hb : d102052 q = 1) : d9803 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d15006, d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d15007 q = 1) (hb : d102052 q = 1) : d9804 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d15007, d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h31 (q : Pattern) (ha : d16661 q = 1) (hb : d102052 q = 1) : d9805 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16661, d9805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d16661, d9805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d16662 q = 1) (hb : d102052 q = 1) : d9806 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16662, d9806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16662, d9806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  exact h32 p ha hb
theorem andIntro45021 (p : Pattern) (ha : d16667 p = 1) (hb : d102052 p = 1) : d9821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9813 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13160 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13160, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d9814 q = 1) (hb : d102052 q = 1) : d9814 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13161 q = 1) (hb : d102052 q = 1) : d9815 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, d9815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13161, d9815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9816 q = 1) (hb : d102052 q = 1) : d9816 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13162 q = 1) (hb : d102052 q = 1) : d9817 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13162, d9817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13162, d9817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13163 q = 1) (hb : d102052 q = 1) : d9818 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13163, d9818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13163, d9818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9799 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15004 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d9800 q = 1) (hb : d102052 q = 1) : d9800 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15005 q = 1) (hb : d102052 q = 1) : d9801 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15005, d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9802 q = 1) (hb : d102052 q = 1) : d9802 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d15006 q = 1) (hb : d102052 q = 1) : d9803 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15006, d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15006, d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15007 q = 1) (hb : d102052 q = 1) : d9804 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15007, d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15007, d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d16666 q = 1) (hb : d102052 q = 1) : d9819 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16666, d9819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16666, d9819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15008 q = 1) (hb : d102052 q = 1) : d9820 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15008, d9820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15008, d9820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d16667 q = 1) (hb : d102052 q = 1) : d9821 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16667, d9821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16667, d9821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45022 (p : Pattern) (ha : d20627 p = 1) (hb : d102052 p = 1) : d20043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16663 q = 1) (hb : d102052 q = 1) : d9807 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16663, d9807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45019 q ha hb
    | true =>
      simp only [d16663, d9807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45020 q ha hb
  have h2 (q : Pattern) (ha : d16664 q = 1) (hb : d102052 q = 1) : d20032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d20032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16664, d20032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16665 q = 1) (hb : d102052 q = 1) : d20033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, d20033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16665, d20033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16668 q = 1) (hb : d102052 q = 1) : d9822 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16668, d9822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45020 q ha hb
    | true =>
      simp only [d16668, d9822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45021 q ha hb
  have h5 (q : Pattern) (ha : d16669 q = 1) (hb : d102052 q = 1) : d20034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d20034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16669, d20034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16670 q = 1) (hb : d102052 q = 1) : d20035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, d20035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16670, d20035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16671 q = 1) (hb : d102052 q = 1) : d20036 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, d20036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16671, d20036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16673 q = 1) (hb : d102052 q = 1) : d9834 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45020 q ha hb
    | true =>
      simp only [d16673, d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
  have h9 (q : Pattern) (ha : d16674 q = 1) (hb : d102052 q = 1) : d20037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16675 q = 1) (hb : d102052 q = 1) : d20038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16676 q = 1) (hb : d102052 q = 1) : d9851 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
    | true =>
      simp only [d16676, d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45018 q ha hb
  have h12 (q : Pattern) (ha : d16677 q = 1) (hb : d102052 q = 1) : d20039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16678 q = 1) (hb : d102052 q = 1) : d20040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16679 q = 1) (hb : d102052 q = 1) : d20041 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16679, d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16680 q = 1) (hb : d102052 q = 1) : d20042 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, d20042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16680, d20042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9855 q = 1) (hb : d102052 q = 1) : d9855 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d20627 q = 1) (hb : d102052 q = 1) : d20043 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20627, d20043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20627, d20043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45023 (p : Pattern) (ha : d20630 p = 1) (hb : d102052 p = 1) : d20048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d102052 q = 1) : d9834 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45020 q ha hb
    | true =>
      simp only [d16673, d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d102052 q = 1) : d20037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d102052 q = 1) : d20038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d102052 q = 1) : d9851 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
    | true =>
      simp only [d16676, d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45018 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d102052 q = 1) : d20039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d102052 q = 1) : d20040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d102052 q = 1) : d20041 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16684 q = 1) (hb : d102052 q = 1) : d20046 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, d20046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16684, d20046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16685 q = 1) (hb : d102052 q = 1) : d20047 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, d20047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16685, d20047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9860 q = 1) (hb : d102052 q = 1) : d9860 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d20630 q = 1) (hb : d102052 q = 1) : d20048 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20630, d20048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20630, d20048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45024 (p : Pattern) (ha : d20636 p = 1) (hb : d102052 p = 1) : d20054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20628 q = 1) (hb : d102052 q = 1) : d20044 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20628, d20044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45022 q ha hb
    | true =>
      simp only [d20628, d20044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20629 q = 1) (hb : d102052 q = 1) : d20045 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20629, d20045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20629, d20045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20631 q = 1) (hb : d102052 q = 1) : d20049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, d20049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45023 q ha hb
    | true =>
      simp only [d20631, d20049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20632 q = 1) (hb : d102052 q = 1) : d20050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, d20050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20632, d20050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20633 q = 1) (hb : d102052 q = 1) : d20051 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20633, d20051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20633, d20051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20634 q = 1) (hb : d102052 q = 1) : d20052 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20634, d20052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20634, d20052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20635 q = 1) (hb : d102052 q = 1) : d20053 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20635, d20053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20635, d20053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20636 q = 1) (hb : d102052 q = 1) : d20054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20636, d20054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20636, d20054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45025 (p : Pattern) (ha : d20643 p = 1) (hb : d102052 p = 1) : d20065 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20631 q = 1) (hb : d102052 q = 1) : d20049 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, d20049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45023 q ha hb
    | true =>
      simp only [d20631, d20049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20632 q = 1) (hb : d102052 q = 1) : d20050 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, d20050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20632, d20050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d102052 q = 1) : d20060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d20060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45015 q ha hb
    | true =>
      simp only [d20638, d20060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d102052 q = 1) : d20061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d20061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d20061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20640 q = 1) (hb : d102052 q = 1) : d20062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20640, d20062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20640, d20062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20641 q = 1) (hb : d102052 q = 1) : d20063 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20641, d20063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20641, d20063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20642 q = 1) (hb : d102052 q = 1) : d20064 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20642, d20064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20642, d20064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20643 q = 1) (hb : d102052 q = 1) : d20065 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20643, d20065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20643, d20065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45026 (p : Pattern) (ha : d13190 p = 1) (hb : d102052 p = 1) : d9987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1391 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1121 q = 1) (hb : d102052 q = 1) : d1121 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1392 q = 1) (hb : d102052 q = 1) : d9829 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1392, d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d102052 q = 1) : d1122 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1393 q = 1) (hb : d102052 q = 1) : d9830 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1393, d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1394 q = 1) (hb : d102052 q = 1) : d9831 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1394, d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1400 q = 1) (hb : d102052 q = 1) : d9868 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d9868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1400, d9868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d13190 q = 1) (hb : d102052 q = 1) : d9987 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, d9987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13190, d9987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro45027 (p : Pattern) (ha : d20661 p = 1) (hb : d102052 p = 1) : d20097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d102052 q = 1) : d9834 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45020 q ha hb
    | true =>
      simp only [d16673, d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d102052 q = 1) : d20037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d102052 q = 1) : d20038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d102052 q = 1) : d9851 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
    | true =>
      simp only [d16676, d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45018 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d102052 q = 1) : d20039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d102052 q = 1) : d20040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d102052 q = 1) : d20041 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16743 q = 1) (hb : d102052 q = 1) : d9988 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d9988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
    | true =>
      simp only [d16743, d9988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45026 q ha hb
  have h9 (q : Pattern) (ha : d16744 q = 1) (hb : d102052 q = 1) : d20093 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d20093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16744, d20093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16745 q = 1) (hb : d102052 q = 1) : d20094 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d20094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16745, d20094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16746 q = 1) (hb : d102052 q = 1) : d20095 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d20095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16746, d20095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16747 q = 1) (hb : d102052 q = 1) : d20096 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d20096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16747, d20096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9992 q = 1) (hb : d102052 q = 1) : d9992 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d20661 q = 1) (hb : d102052 q = 1) : d20097 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20661, d20097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20661, d20097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro45028 (p : Pattern) (ha : d20667 p = 1) (hb : d102052 p = 1) : d20103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20662 q = 1) (hb : d102052 q = 1) : d20098 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20662, d20098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45027 q ha hb
    | true =>
      simp only [d20662, d20098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20663 q = 1) (hb : d102052 q = 1) : d20099 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20663, d20099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20663, d20099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20664 q = 1) (hb : d102052 q = 1) : d20100 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20664, d20100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20664, d20100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20665 q = 1) (hb : d102052 q = 1) : d20101 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20665, d20101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20665, d20101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20666 q = 1) (hb : d102052 q = 1) : d20102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20666, d20102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20666, d20102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20667 q = 1) (hb : d102052 q = 1) : d20103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20667, d20103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20667, d20103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45029 (p : Pattern) (ha : d102052 p = 1) (hb : d130994 p = 1) : d130285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20644 q = 1) (hb : d102052 q = 1) : d20066 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20644, d20066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45024 q ha hb
    | true =>
      simp only [d20644, d20066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45025 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d130990 q = 1) : d130281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130990, d130281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130990, d130281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20668 q = 1) (hb : d102052 q = 1) : d20104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20668, d20104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45028 q ha hb
    | true =>
      simp only [d20668, d20104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20669 q = 1) (hb : d102052 q = 1) : d20105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20669, d20105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20669, d20105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130991 q = 1) : d130282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130991, d130282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130991, d130282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130992 q = 1) : d130283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130992, d130283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130992, d130283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d130993 q = 1) : d130284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130993, d130284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130993, d130284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d130994 q = 1) : d130285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130994, d130285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130994, d130285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45030 (p : Pattern) (ha : d102052 p = 1) (hb : d131000 p = 1) : d130291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d130995 q = 1) : d130286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130995, d130286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130995, d130286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45029 q ha hb
  have h2 (q : Pattern) (ha : d20685 q = 1) (hb : d102052 q = 1) : d20121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20685, d20121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20685, d20121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45017 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d130996 q = 1) : d130287 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130996, d130287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130996, d130287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d130997 q = 1) : d130288 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130997, d130288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130997, d130288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d130998 q = 1) : d130289 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130998, d130289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130998, d130289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d130999 q = 1) : d130290 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130999, d130290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130999, d130290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d131000 q = 1) : d130291 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131000, d130291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131000, d130291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45031 (p : Pattern) (ha : d102052 p = 1) (hb : d131006 p = 1) : d130297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131001 q = 1) : d130292 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131001, d130292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131001, d130292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45030 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d131002 q = 1) : d130293 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131002, d130293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131002, d130293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d131003 q = 1) : d130294 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131003, d130294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131003, d130294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d131004 q = 1) : d130295 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131004, d130295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131004, d130295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131005 q = 1) : d130296 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131005, d130296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131005, d130296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131006 q = 1) : d130297 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131006, d130297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131006, d130297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45032 (p : Pattern) (ha : d15435 p = 1) (hb : d102052 p = 1) : d10163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1868 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1582 q = 1) (hb : d102052 q = 1) : d1582 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1869 q = 1) (hb : d102052 q = 1) : d10159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1869, d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1583 q = 1) (hb : d102052 q = 1) : d1583 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1870 q = 1) (hb : d102052 q = 1) : d10160 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d10160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1870, d10160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1871 q = 1) (hb : d102052 q = 1) : d10161 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1871, d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1877 q = 1) (hb : d102052 q = 1) : d10162 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1877, d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10134 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15412 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d10135 q = 1) (hb : d102052 q = 1) : d10135 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15413 q = 1) (hb : d102052 q = 1) : d10136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15413, d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10137 q = 1) (hb : d102052 q = 1) : d10137 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15414 q = 1) (hb : d102052 q = 1) : d10138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d10138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15414, d10138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15415 q = 1) (hb : d102052 q = 1) : d10139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15415, d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d15416 q = 1) (hb : d102052 q = 1) : d10140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15416, d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d15435 q = 1) (hb : d102052 q = 1) : d10163 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, d10163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15435, d10163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45033 (p : Pattern) (ha : d17032 p = 1) (hb : d102052 p = 1) : d10121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1569 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1862 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1570 q = 1) (hb : d102052 q = 1) : d1570 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1863 q = 1) (hb : d102052 q = 1) : d10111 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d10111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1863, d10111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1571 q = 1) (hb : d102052 q = 1) : d1571 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1864 q = 1) (hb : d102052 q = 1) : d10112 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d10112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1864, d10112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1865 q = 1) (hb : d102052 q = 1) : d10113 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d10113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1865, d10113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10114 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17027 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17027, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10115 q = 1) (hb : d102052 q = 1) : d10115 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17028 q = 1) (hb : d102052 q = 1) : d10116 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d10116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17028, d10116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10117 q = 1) (hb : d102052 q = 1) : d10117 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d17029 q = 1) (hb : d102052 q = 1) : d10118 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17029, d10118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17029, d10118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17030 q = 1) (hb : d102052 q = 1) : d10119 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17030, d10119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17030, d10119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d17031 q = 1) (hb : d102052 q = 1) : d10120 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17031, d10120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17031, d10120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10084 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d15397 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d10085 q = 1) (hb : d102052 q = 1) : d10085 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15398 q = 1) (hb : d102052 q = 1) : d10086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15398, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10087 q = 1) (hb : d102052 q = 1) : d10087 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d15399 q = 1) (hb : d102052 q = 1) : d10088 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15399, d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d15400 q = 1) (hb : d102052 q = 1) : d10089 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15400, d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d15401 q = 1) (hb : d102052 q = 1) : d10105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d15401, d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h25 (q : Pattern) (ha : d17032 q = 1) (hb : d102052 q = 1) : d10121 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17032, d10121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17032, d10121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro45034 (p : Pattern) (ha : d20710 p = 1) (hb : d102052 p = 1) : d20163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17053 q = 1) (hb : d102052 q = 1) : d10164 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
    | true =>
      simp only [d17053, d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45032 q ha hb
  have h2 (q : Pattern) (ha : d17054 q = 1) (hb : d102052 q = 1) : d20159 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d20159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d20159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17055 q = 1) (hb : d102052 q = 1) : d20160 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d20160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d20160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17056 q = 1) (hb : d102052 q = 1) : d20161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d20161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17056, d20161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17057 q = 1) (hb : d102052 q = 1) : d20162 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d20162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17057, d20162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10168 q = 1) (hb : d102052 q = 1) : d10168 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20710 q = 1) (hb : d102052 q = 1) : d20163 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20710, d20163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20710, d20163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45035 (p : Pattern) (ha : d20751 p = 1) (hb : d102052 p = 1) : d20218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20711 q = 1) (hb : d102052 q = 1) : d20164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d20164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45034 q ha hb
    | true =>
      simp only [d20711, d20164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20712 q = 1) (hb : d102052 q = 1) : d20165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d20165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d20165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20748 q = 1) (hb : d102052 q = 1) : d20215 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20748, d20215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20748, d20215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20749 q = 1) (hb : d102052 q = 1) : d20216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20749, d20216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20749, d20216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20750 q = 1) (hb : d102052 q = 1) : d20217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20750, d20217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20750, d20217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20751 q = 1) (hb : d102052 q = 1) : d20218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20751, d20218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20751, d20218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45036 (p : Pattern) (ha : d20757 p = 1) (hb : d102052 p = 1) : d20224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20752 q = 1) (hb : d102052 q = 1) : d20219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20752, d20219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45035 q ha hb
    | true =>
      simp only [d20752, d20219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20753 q = 1) (hb : d102052 q = 1) : d20220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20753, d20220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20753, d20220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20754 q = 1) (hb : d102052 q = 1) : d20221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20754, d20221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20754, d20221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20755 q = 1) (hb : d102052 q = 1) : d20222 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20755, d20222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20755, d20222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20756 q = 1) (hb : d102052 q = 1) : d20223 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20756, d20223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20756, d20223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20757 q = 1) (hb : d102052 q = 1) : d20224 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20757, d20224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20757, d20224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45037 (p : Pattern) (ha : d15417 p = 1) (hb : d102052 p = 1) : d10141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6496 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6496, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5134 q = 1) (hb : d102052 q = 1) : d5134 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6497 q = 1) (hb : d102052 q = 1) : d10125 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, d10125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6497, d10125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5135 q = 1) (hb : d102052 q = 1) : d5135 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6498 q = 1) (hb : d102052 q = 1) : d10126 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6498, d10126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6498, d10126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6499 q = 1) (hb : d102052 q = 1) : d10127 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6499, d10127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6499, d10127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6500 q = 1) (hb : d102052 q = 1) : d10128 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d10128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6500, d10128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10134 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15412 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d10135 q = 1) (hb : d102052 q = 1) : d10135 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15413 q = 1) (hb : d102052 q = 1) : d10136 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15413, d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10137 q = 1) (hb : d102052 q = 1) : d10137 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15414 q = 1) (hb : d102052 q = 1) : d10138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d10138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15414, d10138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15415 q = 1) (hb : d102052 q = 1) : d10139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15415, d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d15416 q = 1) (hb : d102052 q = 1) : d10140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15416, d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d15417 q = 1) (hb : d102052 q = 1) : d10141 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15417, d10141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15417, d10141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45038 (p : Pattern) (ha : d17010 p = 1) (hb : d102052 p = 1) : d10069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1664 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1853 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1665 q = 1) (hb : d102052 q = 1) : d1665 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1854 q = 1) (hb : d102052 q = 1) : d10032 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, d10032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1854, d10032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1666 q = 1) (hb : d102052 q = 1) : d1666 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1855 q = 1) (hb : d102052 q = 1) : d10033 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1855, d10033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1855, d10033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1856 q = 1) (hb : d102052 q = 1) : d10034 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1856, d10034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1856, d10034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10035 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17004 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10036 q = 1) (hb : d102052 q = 1) : d10036 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17005 q = 1) (hb : d102052 q = 1) : d10037 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d10037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17005, d10037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10038 q = 1) (hb : d102052 q = 1) : d10038 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d17006 q = 1) (hb : d102052 q = 1) : d10039 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d10039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17006, d10039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17007 q = 1) (hb : d102052 q = 1) : d10040 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d10040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17007, d10040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d17008 q = 1) (hb : d102052 q = 1) : d10041 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17008, d10041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17008, d10041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10045 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d15380 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d10046 q = 1) (hb : d102052 q = 1) : d10046 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15381 q = 1) (hb : d102052 q = 1) : d10047 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d10047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15381, d10047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10048 q = 1) (hb : d102052 q = 1) : d10048 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d15382 q = 1) (hb : d102052 q = 1) : d10049 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d10049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15382, d10049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d15383 q = 1) (hb : d102052 q = 1) : d10050 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d10050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15383, d10050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d10062 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d15387 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d10063 q = 1) (hb : d102052 q = 1) : d10063 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d15388 q = 1) (hb : d102052 q = 1) : d10064 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d15388, d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d10065 q = 1) (hb : d102052 q = 1) : d10065 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d15389 q = 1) (hb : d102052 q = 1) : d10066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d10066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d15389, d10066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d15390 q = 1) (hb : d102052 q = 1) : d10067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d15390, d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h31 (q : Pattern) (ha : d17009 q = 1) (hb : d102052 q = 1) : d10068 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17009, d10068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d17009, d10068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d17010 q = 1) (hb : d102052 q = 1) : d10069 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17010, d10069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17010, d10069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  exact h32 p ha hb
theorem andIntro45039 (p : Pattern) (ha : d17017 p = 1) (hb : d102052 p = 1) : d10091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1554 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1857 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1555 q = 1) (hb : d102052 q = 1) : d1555 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1858 q = 1) (hb : d102052 q = 1) : d10070 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, d10070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1858, d10070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1556 q = 1) (hb : d102052 q = 1) : d1556 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1859 q = 1) (hb : d102052 q = 1) : d10071 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1859, d10071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1859, d10071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1860 q = 1) (hb : d102052 q = 1) : d10072 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1860, d10072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1860, d10072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10073 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17011 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17011, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10074 q = 1) (hb : d102052 q = 1) : d10074 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17012 q = 1) (hb : d102052 q = 1) : d10075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, d10075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17012, d10075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10076 q = 1) (hb : d102052 q = 1) : d10076 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d17013 q = 1) (hb : d102052 q = 1) : d10077 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17013, d10077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17013, d10077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17014 q = 1) (hb : d102052 q = 1) : d10078 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17014, d10078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17014, d10078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d17015 q = 1) (hb : d102052 q = 1) : d10079 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17015, d10079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17015, d10079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10062 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d15387 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d10063 q = 1) (hb : d102052 q = 1) : d10063 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15388 q = 1) (hb : d102052 q = 1) : d10064 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15388, d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10065 q = 1) (hb : d102052 q = 1) : d10065 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d15389 q = 1) (hb : d102052 q = 1) : d10066 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d10066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15389, d10066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d15390 q = 1) (hb : d102052 q = 1) : d10067 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15390, d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d10084 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d15397 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d10085 q = 1) (hb : d102052 q = 1) : d10085 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d15398 q = 1) (hb : d102052 q = 1) : d10086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d15398, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d10087 q = 1) (hb : d102052 q = 1) : d10087 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d15399 q = 1) (hb : d102052 q = 1) : d10088 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d15399, d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d15400 q = 1) (hb : d102052 q = 1) : d10089 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d15400, d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h31 (q : Pattern) (ha : d17016 q = 1) (hb : d102052 q = 1) : d10090 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17016, d10090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d17016, d10090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d17017 q = 1) (hb : d102052 q = 1) : d10091 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17017, d10091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17017, d10091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  exact h32 p ha hb
theorem andIntro45040 (p : Pattern) (ha : d17022 p = 1) (hb : d102052 p = 1) : d10106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13486 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13486, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d10099 q = 1) (hb : d102052 q = 1) : d10099 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13487 q = 1) (hb : d102052 q = 1) : d10100 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, d10100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13487, d10100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10101 q = 1) (hb : d102052 q = 1) : d10101 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13488 q = 1) (hb : d102052 q = 1) : d10102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13488, d10102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13488, d10102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13489 q = 1) (hb : d102052 q = 1) : d10103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13489, d10103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13489, d10103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10084 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15397 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10085 q = 1) (hb : d102052 q = 1) : d10085 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15398 q = 1) (hb : d102052 q = 1) : d10086 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15398, d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10087 q = 1) (hb : d102052 q = 1) : d10087 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d15399 q = 1) (hb : d102052 q = 1) : d10088 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15399, d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15400 q = 1) (hb : d102052 q = 1) : d10089 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15400, d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d17021 q = 1) (hb : d102052 q = 1) : d10104 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17021, d10104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17021, d10104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15401 q = 1) (hb : d102052 q = 1) : d10105 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15401, d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d17022 q = 1) (hb : d102052 q = 1) : d10106 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17022, d10106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17022, d10106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45041 (p : Pattern) (ha : d20700 p = 1) (hb : d102052 p = 1) : d20147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17018 q = 1) (hb : d102052 q = 1) : d10092 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17018, d10092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45038 q ha hb
    | true =>
      simp only [d17018, d10092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45039 q ha hb
  have h2 (q : Pattern) (ha : d17019 q = 1) (hb : d102052 q = 1) : d20136 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d20136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17019, d20136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17020 q = 1) (hb : d102052 q = 1) : d20137 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, d20137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17020, d20137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17023 q = 1) (hb : d102052 q = 1) : d10107 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17023, d10107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45039 q ha hb
    | true =>
      simp only [d17023, d10107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45040 q ha hb
  have h5 (q : Pattern) (ha : d17024 q = 1) (hb : d102052 q = 1) : d20138 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d20138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17024, d20138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17025 q = 1) (hb : d102052 q = 1) : d20139 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, d20139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17025, d20139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17026 q = 1) (hb : d102052 q = 1) : d20140 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, d20140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17026, d20140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17033 q = 1) (hb : d102052 q = 1) : d10122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45039 q ha hb
    | true =>
      simp only [d17033, d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
  have h9 (q : Pattern) (ha : d17034 q = 1) (hb : d102052 q = 1) : d20141 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17035 q = 1) (hb : d102052 q = 1) : d20142 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17036 q = 1) (hb : d102052 q = 1) : d10142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
    | true =>
      simp only [d17036, d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45037 q ha hb
  have h12 (q : Pattern) (ha : d17037 q = 1) (hb : d102052 q = 1) : d20143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17038 q = 1) (hb : d102052 q = 1) : d20144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17039 q = 1) (hb : d102052 q = 1) : d20145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17039, d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17040 q = 1) (hb : d102052 q = 1) : d20146 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, d20146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17040, d20146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10146 q = 1) (hb : d102052 q = 1) : d10146 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d20700 q = 1) (hb : d102052 q = 1) : d20147 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20700, d20147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20700, d20147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45042 (p : Pattern) (ha : d20703 p = 1) (hb : d102052 p = 1) : d20152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d102052 q = 1) : d10122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45039 q ha hb
    | true =>
      simp only [d17033, d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d102052 q = 1) : d20141 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d102052 q = 1) : d20142 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d102052 q = 1) : d10142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
    | true =>
      simp only [d17036, d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45037 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d102052 q = 1) : d20143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d102052 q = 1) : d20144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d102052 q = 1) : d20145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17044 q = 1) (hb : d102052 q = 1) : d20150 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, d20150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17044, d20150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17045 q = 1) (hb : d102052 q = 1) : d20151 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, d20151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17045, d20151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10151 q = 1) (hb : d102052 q = 1) : d10151 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d20703 q = 1) (hb : d102052 q = 1) : d20152 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20703, d20152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20703, d20152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45043 (p : Pattern) (ha : d20709 p = 1) (hb : d102052 p = 1) : d20158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20701 q = 1) (hb : d102052 q = 1) : d20148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20701, d20148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45041 q ha hb
    | true =>
      simp only [d20701, d20148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20702 q = 1) (hb : d102052 q = 1) : d20149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20702, d20149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20702, d20149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20704 q = 1) (hb : d102052 q = 1) : d20153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, d20153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45042 q ha hb
    | true =>
      simp only [d20704, d20153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20705 q = 1) (hb : d102052 q = 1) : d20154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, d20154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20705, d20154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20706 q = 1) (hb : d102052 q = 1) : d20155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20706, d20155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20706, d20155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20707 q = 1) (hb : d102052 q = 1) : d20156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20707, d20156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20707, d20156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20708 q = 1) (hb : d102052 q = 1) : d20157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20708, d20157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20708, d20157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20709 q = 1) (hb : d102052 q = 1) : d20158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20709, d20158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20709, d20158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45044 (p : Pattern) (ha : d20716 p = 1) (hb : d102052 p = 1) : d20169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20704 q = 1) (hb : d102052 q = 1) : d20153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, d20153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45042 q ha hb
    | true =>
      simp only [d20704, d20153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20705 q = 1) (hb : d102052 q = 1) : d20154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, d20154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20705, d20154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d102052 q = 1) : d20164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d20164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45034 q ha hb
    | true =>
      simp only [d20711, d20164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d102052 q = 1) : d20165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d20165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d20165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20713 q = 1) (hb : d102052 q = 1) : d20166 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20713, d20166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20713, d20166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20714 q = 1) (hb : d102052 q = 1) : d20167 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20714, d20167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20714, d20167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20715 q = 1) (hb : d102052 q = 1) : d20168 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20715, d20168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20715, d20168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20716 q = 1) (hb : d102052 q = 1) : d20169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20716, d20169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20716, d20169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45045 (p : Pattern) (ha : d13516 p = 1) (hb : d102052 p = 1) : d10293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1868 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1582 q = 1) (hb : d102052 q = 1) : d1582 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1869 q = 1) (hb : d102052 q = 1) : d10159 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1869, d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1583 q = 1) (hb : d102052 q = 1) : d1583 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1870 q = 1) (hb : d102052 q = 1) : d10160 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d10160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1870, d10160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1871 q = 1) (hb : d102052 q = 1) : d10161 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1871, d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1877 q = 1) (hb : d102052 q = 1) : d10162 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1877, d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d13516 q = 1) (hb : d102052 q = 1) : d10293 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, d10293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13516, d10293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro45046 (p : Pattern) (ha : d20734 p = 1) (hb : d102052 p = 1) : d20201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d102052 q = 1) : d10122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45039 q ha hb
    | true =>
      simp only [d17033, d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d102052 q = 1) : d20141 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d102052 q = 1) : d20142 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d102052 q = 1) : d10142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
    | true =>
      simp only [d17036, d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45037 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d102052 q = 1) : d20143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d102052 q = 1) : d20144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d102052 q = 1) : d20145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17108 q = 1) (hb : d102052 q = 1) : d10294 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17108, d10294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
    | true =>
      simp only [d17108, d10294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45045 q ha hb
  have h9 (q : Pattern) (ha : d17109 q = 1) (hb : d102052 q = 1) : d20197 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d20197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17109, d20197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17110 q = 1) (hb : d102052 q = 1) : d20198 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, d20198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17110, d20198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17111 q = 1) (hb : d102052 q = 1) : d20199 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, d20199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17111, d20199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17112 q = 1) (hb : d102052 q = 1) : d20200 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, d20200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17112, d20200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10298 q = 1) (hb : d102052 q = 1) : d10298 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d20734 q = 1) (hb : d102052 q = 1) : d20201 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20734, d20201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20734, d20201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro45047 (p : Pattern) (ha : d20740 p = 1) (hb : d102052 p = 1) : d20207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20735 q = 1) (hb : d102052 q = 1) : d20202 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20735, d20202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45046 q ha hb
    | true =>
      simp only [d20735, d20202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20736 q = 1) (hb : d102052 q = 1) : d20203 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20736, d20203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20736, d20203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20737 q = 1) (hb : d102052 q = 1) : d20204 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20737, d20204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20737, d20204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20738 q = 1) (hb : d102052 q = 1) : d20205 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20738, d20205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20738, d20205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20739 q = 1) (hb : d102052 q = 1) : d20206 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20739, d20206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20739, d20206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20740 q = 1) (hb : d102052 q = 1) : d20207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20740, d20207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20740, d20207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45048 (p : Pattern) (ha : d102052 p = 1) (hb : d131014 p = 1) : d130305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20717 q = 1) (hb : d102052 q = 1) : d20170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20717, d20170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45043 q ha hb
    | true =>
      simp only [d20717, d20170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45044 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d131010 q = 1) : d130301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131010, d130301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131010, d130301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20741 q = 1) (hb : d102052 q = 1) : d20208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20741, d20208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45047 q ha hb
    | true =>
      simp only [d20741, d20208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20742 q = 1) (hb : d102052 q = 1) : d20209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20742, d20209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20742, d20209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131011 q = 1) : d130302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131011, d130302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131011, d130302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131012 q = 1) : d130303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131012, d130303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131012, d130303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d131013 q = 1) : d130304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131013, d130304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131013, d130304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d131014 q = 1) : d130305 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131014, d130305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131014, d130305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45049 (p : Pattern) (ha : d102052 p = 1) (hb : d131020 p = 1) : d130311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131015 q = 1) : d130306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131015, d130306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131015, d130306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45048 q ha hb
  have h2 (q : Pattern) (ha : d20758 q = 1) (hb : d102052 q = 1) : d20225 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20758, d20225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20758, d20225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45036 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d131016 q = 1) : d130307 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131016, d130307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131016, d130307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d131017 q = 1) : d130308 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131017, d130308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131017, d130308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131018 q = 1) : d130309 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131018, d130309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131018, d130309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131019 q = 1) : d130310 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131019, d130310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131019, d130310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d131020 q = 1) : d130311 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131020, d130311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131020, d130311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45050 (p : Pattern) (ha : d102052 p = 1) (hb : d131026 p = 1) : d130317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131021 q = 1) : d130312 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131021, d130312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131021, d130312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45049 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d131022 q = 1) : d130313 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131022, d130313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131022, d130313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d131023 q = 1) : d130314 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131023, d130314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131023, d130314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d131024 q = 1) : d130315 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131024, d130315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131024, d130315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131025 q = 1) : d130316 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131025, d130316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131025, d130316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131026 q = 1) : d130317 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131026, d130317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131026, d130317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45051 (p : Pattern) (ha : d15813 p = 1) (hb : d102052 p = 1) : d10440 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2064 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2346 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2065 q = 1) (hb : d102052 q = 1) : d2065 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2347 q = 1) (hb : d102052 q = 1) : d10436 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2347, d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2066 q = 1) (hb : d102052 q = 1) : d2066 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2348 q = 1) (hb : d102052 q = 1) : d10437 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d10437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2348, d10437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2349 q = 1) (hb : d102052 q = 1) : d10438 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2349, d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2355 q = 1) (hb : d102052 q = 1) : d10439 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2355, d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10411 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15790 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d10412 q = 1) (hb : d102052 q = 1) : d10412 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15791 q = 1) (hb : d102052 q = 1) : d10413 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15791, d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10414 q = 1) (hb : d102052 q = 1) : d10414 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15792 q = 1) (hb : d102052 q = 1) : d10415 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d10415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15792, d10415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15793 q = 1) (hb : d102052 q = 1) : d10416 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15793, d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d15794 q = 1) (hb : d102052 q = 1) : d10417 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15794, d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d15813 q = 1) (hb : d102052 q = 1) : d10440 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15813, d10440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15813, d10440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45052 (p : Pattern) (ha : d17396 p = 1) (hb : d102052 p = 1) : d10397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2340 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2053 q = 1) (hb : d102052 q = 1) : d2053 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2341 q = 1) (hb : d102052 q = 1) : d10387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d10387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2341, d10387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2054 q = 1) (hb : d102052 q = 1) : d2054 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2342 q = 1) (hb : d102052 q = 1) : d10388 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d10388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2342, d10388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2343 q = 1) (hb : d102052 q = 1) : d10389 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d10389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2343, d10389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10390 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17391 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10391 q = 1) (hb : d102052 q = 1) : d10391 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17392 q = 1) (hb : d102052 q = 1) : d10392 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, d10392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17392, d10392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10393 q = 1) (hb : d102052 q = 1) : d10393 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d17393 q = 1) (hb : d102052 q = 1) : d10394 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17393, d10394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17393, d10394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17394 q = 1) (hb : d102052 q = 1) : d10395 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17394, d10395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17394, d10395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d17395 q = 1) (hb : d102052 q = 1) : d10396 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17395, d10396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17395, d10396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10370 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d15775 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d10371 q = 1) (hb : d102052 q = 1) : d10371 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d15776 q = 1) (hb : d102052 q = 1) : d10372 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d15776, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10373 q = 1) (hb : d102052 q = 1) : d10373 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d15777 q = 1) (hb : d102052 q = 1) : d10374 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15777, d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d15778 q = 1) (hb : d102052 q = 1) : d10375 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d15778, d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d15779 q = 1) (hb : d102052 q = 1) : d10381 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d15779, d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h25 (q : Pattern) (ha : d17396 q = 1) (hb : d102052 q = 1) : d10397 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17396, d10397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17396, d10397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro45053 (p : Pattern) (ha : d20784 p = 1) (hb : d102052 p = 1) : d20268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17417 q = 1) (hb : d102052 q = 1) : d10441 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
    | true =>
      simp only [d17417, d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45051 q ha hb
  have h2 (q : Pattern) (ha : d17418 q = 1) (hb : d102052 q = 1) : d20264 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d20264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d20264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17419 q = 1) (hb : d102052 q = 1) : d20265 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d20265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d20265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17420 q = 1) (hb : d102052 q = 1) : d20266 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d20266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17420, d20266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17421 q = 1) (hb : d102052 q = 1) : d20267 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, d20267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17421, d20267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10445 q = 1) (hb : d102052 q = 1) : d10445 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20784 q = 1) (hb : d102052 q = 1) : d20268 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20784, d20268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20784, d20268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45054 (p : Pattern) (ha : d20825 p = 1) (hb : d102052 p = 1) : d20323 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20785 q = 1) (hb : d102052 q = 1) : d20269 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d20269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45053 q ha hb
    | true =>
      simp only [d20785, d20269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20786 q = 1) (hb : d102052 q = 1) : d20270 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d20270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d20270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20822 q = 1) (hb : d102052 q = 1) : d20320 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20822, d20320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20822, d20320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20823 q = 1) (hb : d102052 q = 1) : d20321 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20823, d20321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20823, d20321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20824 q = 1) (hb : d102052 q = 1) : d20322 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20824, d20322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20824, d20322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20825 q = 1) (hb : d102052 q = 1) : d20323 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20825, d20323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20825, d20323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45055 (p : Pattern) (ha : d20831 p = 1) (hb : d102052 p = 1) : d20329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20826 q = 1) (hb : d102052 q = 1) : d20324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20826, d20324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45054 q ha hb
    | true =>
      simp only [d20826, d20324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20827 q = 1) (hb : d102052 q = 1) : d20325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20827, d20325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20827, d20325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20828 q = 1) (hb : d102052 q = 1) : d20326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20828, d20326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20828, d20326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20829 q = 1) (hb : d102052 q = 1) : d20327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20829, d20327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20829, d20327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20830 q = 1) (hb : d102052 q = 1) : d20328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20830, d20328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20830, d20328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20831 q = 1) (hb : d102052 q = 1) : d20329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20831, d20329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20831, d20329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45056 (p : Pattern) (ha : d15795 p = 1) (hb : d102052 p = 1) : d10418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6643 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5247 q = 1) (hb : d102052 q = 1) : d5247 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6644 q = 1) (hb : d102052 q = 1) : d10401 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6644, d10401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6644, d10401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5248 q = 1) (hb : d102052 q = 1) : d5248 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6645 q = 1) (hb : d102052 q = 1) : d10402 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d6645, d10402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6645, d10402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6646 q = 1) (hb : d102052 q = 1) : d10403 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d6646, d10403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6646, d10403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6647 q = 1) (hb : d102052 q = 1) : d10404 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d10404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6647, d10404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10411 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15790 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d10412 q = 1) (hb : d102052 q = 1) : d10412 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15791 q = 1) (hb : d102052 q = 1) : d10413 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15791, d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10414 q = 1) (hb : d102052 q = 1) : d10414 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15792 q = 1) (hb : d102052 q = 1) : d10415 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d10415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15792, d10415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15793 q = 1) (hb : d102052 q = 1) : d10416 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15793, d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d15794 q = 1) (hb : d102052 q = 1) : d10417 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15794, d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d15795 q = 1) (hb : d102052 q = 1) : d10418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15795, d10418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15795, d10418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45057 (p : Pattern) (ha : d17375 p = 1) (hb : d102052 p = 1) : d10359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2143 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2331 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2144 q = 1) (hb : d102052 q = 1) : d2144 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2332 q = 1) (hb : d102052 q = 1) : d10339 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2332, d10339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2332, d10339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2145 q = 1) (hb : d102052 q = 1) : d2145 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2333 q = 1) (hb : d102052 q = 1) : d10340 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2333, d10340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2333, d10340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2334 q = 1) (hb : d102052 q = 1) : d10341 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2334, d10341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2334, d10341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10342 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17369 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10343 q = 1) (hb : d102052 q = 1) : d10343 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17370 q = 1) (hb : d102052 q = 1) : d10344 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d10344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17370, d10344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10345 q = 1) (hb : d102052 q = 1) : d10345 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d17371 q = 1) (hb : d102052 q = 1) : d10346 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d10346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17371, d10346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17372 q = 1) (hb : d102052 q = 1) : d10347 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d10347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17372, d10347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d17373 q = 1) (hb : d102052 q = 1) : d10348 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17373, d10348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17373, d10348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10352 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d13813 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d10353 q = 1) (hb : d102052 q = 1) : d10353 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d13814 q = 1) (hb : d102052 q = 1) : d10354 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d13814, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10355 q = 1) (hb : d102052 q = 1) : d10355 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d13815 q = 1) (hb : d102052 q = 1) : d10356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13815, d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d13816 q = 1) (hb : d102052 q = 1) : d10357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d13816, d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d17374 q = 1) (hb : d102052 q = 1) : d10358 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17374, d10358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17374, d10358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d17375 q = 1) (hb : d102052 q = 1) : d10359 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17375, d10359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17375, d10359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro45058 (p : Pattern) (ha : d17382 p = 1) (hb : d102052 p = 1) : d10377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2335 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2035 q = 1) (hb : d102052 q = 1) : d2035 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2336 q = 1) (hb : d102052 q = 1) : d10360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d10360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2336, d10360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2036 q = 1) (hb : d102052 q = 1) : d2036 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2337 q = 1) (hb : d102052 q = 1) : d10361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d10361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2337, d10361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2338 q = 1) (hb : d102052 q = 1) : d10362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d10362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2338, d10362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10363 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17376 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10364 q = 1) (hb : d102052 q = 1) : d10364 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d17377 q = 1) (hb : d102052 q = 1) : d10365 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d10365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17377, d10365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10366 q = 1) (hb : d102052 q = 1) : d10366 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d17378 q = 1) (hb : d102052 q = 1) : d10367 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d10367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d17378, d10367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17379 q = 1) (hb : d102052 q = 1) : d10368 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d10368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d17379, d10368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d17380 q = 1) (hb : d102052 q = 1) : d10369 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17380, d10369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17380, d10369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d10352 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d13813 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d10353 q = 1) (hb : d102052 q = 1) : d10353 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d13814 q = 1) (hb : d102052 q = 1) : d10354 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d13814, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10355 q = 1) (hb : d102052 q = 1) : d10355 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d13815 q = 1) (hb : d102052 q = 1) : d10356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13815, d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d13816 q = 1) (hb : d102052 q = 1) : d10357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d13816, d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d10370 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d15775 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d10371 q = 1) (hb : d102052 q = 1) : d10371 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d15776 q = 1) (hb : d102052 q = 1) : d10372 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d15776, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d10373 q = 1) (hb : d102052 q = 1) : d10373 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d15777 q = 1) (hb : d102052 q = 1) : d10374 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d15777, d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d15778 q = 1) (hb : d102052 q = 1) : d10375 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d15778, d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h31 (q : Pattern) (ha : d17381 q = 1) (hb : d102052 q = 1) : d10376 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d17381, d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d17382 q = 1) (hb : d102052 q = 1) : d10377 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17382, d10377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17382, d10377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  exact h32 p ha hb
theorem andIntro45059 (p : Pattern) (ha : d17386 p = 1) (hb : d102052 p = 1) : d10382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10352 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13813 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d10353 q = 1) (hb : d102052 q = 1) : d10353 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13814 q = 1) (hb : d102052 q = 1) : d10354 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13814, d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10355 q = 1) (hb : d102052 q = 1) : d10355 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13815 q = 1) (hb : d102052 q = 1) : d10356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13815, d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13816 q = 1) (hb : d102052 q = 1) : d10357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13816, d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10370 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15775 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10371 q = 1) (hb : d102052 q = 1) : d10371 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15776 q = 1) (hb : d102052 q = 1) : d10372 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15776, d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10373 q = 1) (hb : d102052 q = 1) : d10373 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d15777 q = 1) (hb : d102052 q = 1) : d10374 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15777, d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15778 q = 1) (hb : d102052 q = 1) : d10375 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15778, d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d17381 q = 1) (hb : d102052 q = 1) : d10376 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17381, d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17381, d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15779 q = 1) (hb : d102052 q = 1) : d10381 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15779, d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h18 (q : Pattern) (ha : d17386 q = 1) (hb : d102052 q = 1) : d10382 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17386, d10382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d17386, d10382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro45060 (p : Pattern) (ha : d20774 p = 1) (hb : d102052 p = 1) : d20252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17383 q = 1) (hb : d102052 q = 1) : d10378 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d10378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45057 q ha hb
    | true =>
      simp only [d17383, d10378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45058 q ha hb
  have h2 (q : Pattern) (ha : d17384 q = 1) (hb : d102052 q = 1) : d20241 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d20241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17384, d20241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17385 q = 1) (hb : d102052 q = 1) : d20242 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d20242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17385, d20242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17387 q = 1) (hb : d102052 q = 1) : d10383 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d10383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45058 q ha hb
    | true =>
      simp only [d17387, d10383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45059 q ha hb
  have h5 (q : Pattern) (ha : d17388 q = 1) (hb : d102052 q = 1) : d20243 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d20243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17388, d20243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17389 q = 1) (hb : d102052 q = 1) : d20244 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d20244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17389, d20244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17390 q = 1) (hb : d102052 q = 1) : d20245 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d20245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17390, d20245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17397 q = 1) (hb : d102052 q = 1) : d10398 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45058 q ha hb
    | true =>
      simp only [d17397, d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
  have h9 (q : Pattern) (ha : d17398 q = 1) (hb : d102052 q = 1) : d20246 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17399 q = 1) (hb : d102052 q = 1) : d20247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17400 q = 1) (hb : d102052 q = 1) : d10419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
    | true =>
      simp only [d17400, d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45056 q ha hb
  have h12 (q : Pattern) (ha : d17401 q = 1) (hb : d102052 q = 1) : d20248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17402 q = 1) (hb : d102052 q = 1) : d20249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17403 q = 1) (hb : d102052 q = 1) : d20250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17403, d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17404 q = 1) (hb : d102052 q = 1) : d20251 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d20251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17404, d20251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10423 q = 1) (hb : d102052 q = 1) : d10423 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d20774 q = 1) (hb : d102052 q = 1) : d20252 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20774, d20252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20774, d20252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45061 (p : Pattern) (ha : d20777 p = 1) (hb : d102052 p = 1) : d20257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d102052 q = 1) : d10398 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45058 q ha hb
    | true =>
      simp only [d17397, d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d102052 q = 1) : d20246 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d102052 q = 1) : d20247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d102052 q = 1) : d10419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
    | true =>
      simp only [d17400, d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45056 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d102052 q = 1) : d20248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d102052 q = 1) : d20249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d102052 q = 1) : d20250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17408 q = 1) (hb : d102052 q = 1) : d20255 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d20255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17408, d20255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17409 q = 1) (hb : d102052 q = 1) : d20256 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d20256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17409, d20256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10428 q = 1) (hb : d102052 q = 1) : d10428 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d20777 q = 1) (hb : d102052 q = 1) : d20257 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20777, d20257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20777, d20257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45062 (p : Pattern) (ha : d20783 p = 1) (hb : d102052 p = 1) : d20263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20775 q = 1) (hb : d102052 q = 1) : d20253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20775, d20253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45060 q ha hb
    | true =>
      simp only [d20775, d20253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20776 q = 1) (hb : d102052 q = 1) : d20254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20776, d20254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20776, d20254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20778 q = 1) (hb : d102052 q = 1) : d20258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, d20258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45061 q ha hb
    | true =>
      simp only [d20778, d20258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20779 q = 1) (hb : d102052 q = 1) : d20259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, d20259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20779, d20259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20780 q = 1) (hb : d102052 q = 1) : d20260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20780, d20260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20780, d20260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20781 q = 1) (hb : d102052 q = 1) : d20261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20781, d20261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20781, d20261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20782 q = 1) (hb : d102052 q = 1) : d20262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20782, d20262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20782, d20262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20783 q = 1) (hb : d102052 q = 1) : d20263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20783, d20263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20783, d20263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45063 (p : Pattern) (ha : d20790 p = 1) (hb : d102052 p = 1) : d20274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20778 q = 1) (hb : d102052 q = 1) : d20258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, d20258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45061 q ha hb
    | true =>
      simp only [d20778, d20258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20779 q = 1) (hb : d102052 q = 1) : d20259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, d20259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20779, d20259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d102052 q = 1) : d20269 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d20269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45053 q ha hb
    | true =>
      simp only [d20785, d20269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d102052 q = 1) : d20270 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d20270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d20270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20787 q = 1) (hb : d102052 q = 1) : d20271 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20787, d20271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20787, d20271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20788 q = 1) (hb : d102052 q = 1) : d20272 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20788, d20272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20788, d20272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20789 q = 1) (hb : d102052 q = 1) : d20273 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20789, d20273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20789, d20273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20790 q = 1) (hb : d102052 q = 1) : d20274 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20790, d20274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20790, d20274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45064 (p : Pattern) (ha : d13843 p = 1) (hb : d102052 p = 1) : d10559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2064 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2346 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d2065 q = 1) (hb : d102052 q = 1) : d2065 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2347 q = 1) (hb : d102052 q = 1) : d10436 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2347, d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2066 q = 1) (hb : d102052 q = 1) : d2066 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2348 q = 1) (hb : d102052 q = 1) : d10437 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d10437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2348, d10437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2349 q = 1) (hb : d102052 q = 1) : d10438 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2349, d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2355 q = 1) (hb : d102052 q = 1) : d10439 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2355, d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d13843 q = 1) (hb : d102052 q = 1) : d10559 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, d10559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13843, d10559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro45065 (p : Pattern) (ha : d20808 p = 1) (hb : d102052 p = 1) : d20306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d102052 q = 1) : d10398 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45058 q ha hb
    | true =>
      simp only [d17397, d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d102052 q = 1) : d20246 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d102052 q = 1) : d20247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d102052 q = 1) : d10419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
    | true =>
      simp only [d17400, d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45056 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d102052 q = 1) : d20248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d102052 q = 1) : d20249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d102052 q = 1) : d20250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17472 q = 1) (hb : d102052 q = 1) : d10560 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17472, d10560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
    | true =>
      simp only [d17472, d10560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45064 q ha hb
  have h9 (q : Pattern) (ha : d17473 q = 1) (hb : d102052 q = 1) : d20302 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d20302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17473, d20302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17474 q = 1) (hb : d102052 q = 1) : d20303 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, d20303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17474, d20303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17475 q = 1) (hb : d102052 q = 1) : d20304 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, d20304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17475, d20304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17476 q = 1) (hb : d102052 q = 1) : d20305 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, d20305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17476, d20305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10564 q = 1) (hb : d102052 q = 1) : d10564 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d20808 q = 1) (hb : d102052 q = 1) : d20306 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20808, d20306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20808, d20306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro45066 (p : Pattern) (ha : d20814 p = 1) (hb : d102052 p = 1) : d20312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20809 q = 1) (hb : d102052 q = 1) : d20307 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20809, d20307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45065 q ha hb
    | true =>
      simp only [d20809, d20307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20810 q = 1) (hb : d102052 q = 1) : d20308 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20810, d20308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20810, d20308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20811 q = 1) (hb : d102052 q = 1) : d20309 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20811, d20309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20811, d20309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20812 q = 1) (hb : d102052 q = 1) : d20310 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20812, d20310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20812, d20310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20813 q = 1) (hb : d102052 q = 1) : d20311 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20813, d20311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20813, d20311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20814 q = 1) (hb : d102052 q = 1) : d20312 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20814, d20312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20814, d20312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45067 (p : Pattern) (ha : d102052 p = 1) (hb : d131035 p = 1) : d130326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20791 q = 1) (hb : d102052 q = 1) : d20275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20791, d20275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45062 q ha hb
    | true =>
      simp only [d20791, d20275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45063 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d131031 q = 1) : d130322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131031, d130322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131031, d130322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d20815 q = 1) (hb : d102052 q = 1) : d20313 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20815, d20313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45066 q ha hb
    | true =>
      simp only [d20815, d20313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20816 q = 1) (hb : d102052 q = 1) : d20314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20816, d20314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20816, d20314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131032 q = 1) : d130323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131032, d130323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131032, d130323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131033 q = 1) : d130324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131033, d130324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131033, d130324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d131034 q = 1) : d130325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131034, d130325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131034, d130325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d131035 q = 1) : d130326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131035, d130326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131035, d130326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45068 (p : Pattern) (ha : d102052 p = 1) (hb : d131041 p = 1) : d130332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131036 q = 1) : d130327 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131036, d130327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131036, d130327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45067 q ha hb
  have h2 (q : Pattern) (ha : d20832 q = 1) (hb : d102052 q = 1) : d20330 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20832, d20330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20832, d20330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45055 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d131037 q = 1) : d130328 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131037, d130328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131037, d130328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d131038 q = 1) : d130329 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131038, d130329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131038, d130329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131039 q = 1) : d130330 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131039, d130330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131039, d130330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131040 q = 1) : d130331 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131040, d130331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131040, d130331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d131041 q = 1) : d130332 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131041, d130332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131041, d130332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45069 (p : Pattern) (ha : d102052 p = 1) (hb : d131047 p = 1) : d130338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131042 q = 1) : d130333 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131042, d130333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131042, d130333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45068 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d131043 q = 1) : d130334 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131043, d130334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131043, d130334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d131044 q = 1) : d130335 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131044, d130335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131044, d130335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d131045 q = 1) : d130336 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131045, d130336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131045, d130336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131046 q = 1) : d130337 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131046, d130337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131046, d130337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131047 q = 1) : d130338 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131047, d130338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d131047, d130338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45070 (p : Pattern) (ha : d102052 p = 1) (hb : d131053 p = 1) : d130344 p = 1 := by
  have h0 (q : Pattern) (ha : d102052 q = 1) (hb : d130970 q = 1) : d130261 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130970, d130261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44983 q ha hb
    | true =>
      simp only [d130970, d130261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44996 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d130988 q = 1) : d130279 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130988, d130279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130988, d130279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45012 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d130989 q = 1) : d130280 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130989, d130280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130989, d130280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d131007 q = 1) : d130298 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131007, d130298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131007, d130298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45031 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131008 q = 1) : d130299 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131008, d130299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131008, d130299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131009 q = 1) : d130300 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131009, d130300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131009, d130300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d131027 q = 1) : d130318 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131027, d130318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131027, d130318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45050 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d131028 q = 1) : d130319 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131028, d130319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131028, d130319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d102052 q = 1) (hb : d131029 q = 1) : d130320 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131029, d130320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131029, d130320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d102052 q = 1) (hb : d131030 q = 1) : d130321 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131030, d130321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131030, d130321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102052 q = 1) (hb : d131048 q = 1) : d130339 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131048, d130339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131048, d130339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45069 q ha hb
  have h12 (q : Pattern) (ha : d102052 q = 1) (hb : d131049 q = 1) : d130340 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131049, d130340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131049, d130340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102052 q = 1) (hb : d131050 q = 1) : d130341 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131050, d130341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131050, d130341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102052 q = 1) (hb : d131051 q = 1) : d130342 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131051, d130342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131051, d130342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102052 q = 1) (hb : d131052 q = 1) : d130343 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131052, d130343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131052, d130343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d102052 q = 1) (hb : d131053 q = 1) : d130344 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131053, d130344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131053, d130344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro45071 (p : Pattern) (ha : d102052 p = 1) (hb : d131059 p = 1) : d130350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131054 q = 1) : d130345 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131054, d130345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45070 q ha hb
    | true =>
      simp only [d131054, d130345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d131055 q = 1) : d130346 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131055, d130346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131055, d130346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d131056 q = 1) : d130347 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131056, d130347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131056, d130347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d131057 q = 1) : d130348 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131057, d130348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131057, d130348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131058 q = 1) : d130349 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131058, d130349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131058, d130349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131059 q = 1) : d130350 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131059, d130350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131059, d130350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45072 (p : Pattern) (ha : d102052 p = 1) (hb : d131065 p = 1) : d130356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131060 q = 1) : d130351 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131060, d130351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45071 q ha hb
    | true =>
      simp only [d131060, d130351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d131061 q = 1) : d130352 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131061, d130352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131061, d130352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d131062 q = 1) : d130353 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131062, d130353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131062, d130353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d131063 q = 1) : d130354 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131063, d130354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131063, d130354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131064 q = 1) : d130355 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131064, d130355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131064, d130355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131065 q = 1) : d130356 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131065, d130356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131065, d130356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45073 (p : Pattern) (ha : d102052 p = 1) (hb : d131071 p = 1) : d130362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131066 q = 1) : d130357 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131066, d130357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45072 q ha hb
    | true =>
      simp only [d131066, d130357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d131067 q = 1) : d130358 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131067, d130358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131067, d130358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d131068 q = 1) : d130359 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131068, d130359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131068, d130359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d131069 q = 1) : d130360 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131069, d130360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131069, d130360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d131070 q = 1) : d130361 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131070, d130361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131070, d130361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d131071 q = 1) : d130362 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131071, d130362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131071, d130362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45074 (p : Pattern) (ha : d131077 p = 1) (hb : d190594 p = 1) : d130368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d131072 q = 1) : d130363 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131072, d130363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45073 q ha hb
    | true =>
      simp only [d131072, d130363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131073 q = 1) (hb : d190594 q = 1) : d130364 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131073, d190594, d130364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131073, d190594, d130364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d190594 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131074 q = 1) (hb : d190594 q = 1) : d130365 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131074, d130365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131074, d130365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131075 q = 1) (hb : d190594 q = 1) : d130366 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131075, d130366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131075, d130366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d131076 q = 1) (hb : d190594 q = 1) : d130367 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131076, d130367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131076, d130367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d131077 q = 1) (hb : d190594 q = 1) : d130368 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131077, d130368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131077, d130368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro45075 (p : Pattern) (ha : d131083 p = 1) (hb : d190594 p = 1) : d130374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131078 q = 1) (hb : d190594 q = 1) : d130369 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131078, d130369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45074 q ha hb
    | true =>
      simp only [d131078, d130369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131079 q = 1) (hb : d190594 q = 1) : d130370 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131079, d130370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131079, d130370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131080 q = 1) (hb : d190594 q = 1) : d130371 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131080, d130371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131080, d130371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131081 q = 1) (hb : d190594 q = 1) : d130372 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131081, d130372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131081, d130372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131082 q = 1) (hb : d190594 q = 1) : d130373 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131082, d130373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131082, d130373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131083 q = 1) (hb : d190594 q = 1) : d130374 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131083, d130374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131083, d130374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45076 (p : Pattern) (ha : d131089 p = 1) (hb : d190594 p = 1) : d130380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131084 q = 1) (hb : d190594 q = 1) : d130375 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131084, d130375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45075 q ha hb
    | true =>
      simp only [d131084, d130375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131085 q = 1) (hb : d190594 q = 1) : d130376 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131085, d130376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131085, d130376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131086 q = 1) (hb : d190594 q = 1) : d130377 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131086, d130377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131086, d130377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131087 q = 1) (hb : d190594 q = 1) : d130378 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131087, d130378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131087, d130378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131088 q = 1) (hb : d190594 q = 1) : d130379 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131088, d130379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131088, d130379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131089 q = 1) (hb : d190594 q = 1) : d130380 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131089, d130380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131089, d130380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45077 (p : Pattern) (ha : d131095 p = 1) (hb : d190594 p = 1) : d130386 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131090 q = 1) (hb : d190594 q = 1) : d130381 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131090, d130381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45076 q ha hb
    | true =>
      simp only [d131090, d130381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131091 q = 1) (hb : d190594 q = 1) : d130382 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131091, d130382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131091, d130382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131092 q = 1) (hb : d190594 q = 1) : d130383 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131092, d130383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131092, d130383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131093 q = 1) (hb : d190594 q = 1) : d130384 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131093, d130384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131093, d130384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131094 q = 1) (hb : d190594 q = 1) : d130385 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131094, d130385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131094, d130385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131095 q = 1) (hb : d190594 q = 1) : d130386 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131095, d130386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131095, d130386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45078 (p : Pattern) (ha : d19742 p = 1) (hb : d129677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19738 q = 1) (hb : d129673 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19738, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19739 q = 1) (hb : d129674 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19740 q = 1) (hb : d129675 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19740, d129675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19740, d129675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19741 q = 1) (hb : d129676 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19741, d129676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19741, d129676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9300 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9301 q = 1) (hb : d100952 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19742 q = 1) (hb : d129677 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19742, d129677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19742, d129677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro45079 (p : Pattern) (ha : d19748 p = 1) (hb : d129683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19743 q = 1) (hb : d129678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19743, d129678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45078 q ha hb
    | true =>
      simp only [d19743, d129678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19744 q = 1) (hb : d129679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19744, d129679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19744, d129679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19745 q = 1) (hb : d129680 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19745, d129680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19745, d129680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19746 q = 1) (hb : d129681 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19746, d129681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19746, d129681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19747 q = 1) (hb : d129682 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19747, d129682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19747, d129682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19748 q = 1) (hb : d129683 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19748, d129683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19748, d129683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45080 (p : Pattern) (ha : d19754 p = 1) (hb : d129689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19749 q = 1) (hb : d129684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d129684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45079 q ha hb
    | true =>
      simp only [d19749, d129684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19750 q = 1) (hb : d129685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19750, d129685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19750, d129685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19751 q = 1) (hb : d129686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19751, d129686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19751, d129686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19752 q = 1) (hb : d129687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19752, d129687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19752, d129687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19753 q = 1) (hb : d129688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19753, d129688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19753, d129688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19754 q = 1) (hb : d129689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19754, d129689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19754, d129689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45081 (p : Pattern) (ha : d19760 p = 1) (hb : d129695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19755 q = 1) (hb : d129690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19755, d129690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19755, d129690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45080 q ha hb
  have h2 (q : Pattern) (ha : d19756 q = 1) (hb : d129691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d19756, d129691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19756, d129691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19757 q = 1) (hb : d129692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d19757, d129692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19757, d129692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19758 q = 1) (hb : d129693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d19758, d129693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19758, d129693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19759 q = 1) (hb : d129694 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d19759, d129694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19759, d129694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19760 q = 1) (hb : d129695 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d19760, d129695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19760, d129695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45082 (p : Pattern) (ha : d19769 p = 1) (hb : d129704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h2 (q : Pattern) (ha : d19765 q = 1) (hb : d129700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19766 q = 1) (hb : d129701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19738 q = 1) (hb : d129673 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19738, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19739 q = 1) (hb : d129674 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19767 q = 1) (hb : d129702 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19767, d129702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19767, d129702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19740 q = 1) (hb : d129675 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19740, d129675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19740, d129675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19768 q = 1) (hb : d129703 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19768, d129703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19768, d129703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9333 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9300 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9334 q = 1) (hb : d100985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19769 q = 1) (hb : d129704 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19769, d129704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19769, d129704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45083 (p : Pattern) (ha : d19775 p = 1) (hb : d129710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19770 q = 1) (hb : d129705 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d129705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45082 q ha hb
    | true =>
      simp only [d19770, d129705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19771 q = 1) (hb : d129706 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d129706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d129706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19743 q = 1) (hb : d129678 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19743, d129678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45078 q ha hb
    | true =>
      simp only [d19743, d129678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19744 q = 1) (hb : d129679 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19744, d129679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19744, d129679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19772 q = 1) (hb : d129707 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19772, d129707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19772, d129707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19773 q = 1) (hb : d129708 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19773, d129708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19773, d129708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19774 q = 1) (hb : d129709 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19774, d129709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19774, d129709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19775 q = 1) (hb : d129710 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19775, d129710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19775, d129710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45084 (p : Pattern) (ha : d129716 p = 1) (hb : d130215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19776 q = 1) (hb : d129711 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19776, d129711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45083 q ha hb
    | true =>
      simp only [d19776, d129711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45079 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129684 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129712 q = 1) (hb : d130211 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129712, d130211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129712, d130211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19749 q = 1) (hb : d129684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d129684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45079 q ha hb
    | true =>
      simp only [d19749, d129684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19750 q = 1) (hb : d129685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19750, d129685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19750, d129685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129713 q = 1) (hb : d130212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129713, d130212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129713, d130212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d129714 q = 1) (hb : d130213 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129714, d130213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129714, d130213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129715 q = 1) (hb : d130214 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129715, d130214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129715, d130214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129716 q = 1) (hb : d130215 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129716, d130215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129716, d130215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro45085 (p : Pattern) (ha : d129722 p = 1) (hb : d130221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129717 q = 1) (hb : d130216 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129717, d130216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129717, d130216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45084 q ha hb
  have h2 (q : Pattern) (ha : d129718 q = 1) (hb : d130217 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129718, d130217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129718, d130217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129719 q = 1) (hb : d130218 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129719, d130218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129719, d130218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129720 q = 1) (hb : d130219 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129720, d130219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129720, d130219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129721 q = 1) (hb : d130220 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129721, d130220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129721, d130220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129722 q = 1) (hb : d130221 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129722, d130221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129722, d130221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45086 (p : Pattern) (ha : d19845 p = 1) (hb : d129756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19749 q = 1) (hb : d129684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d129684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45079 q ha hb
    | true =>
      simp only [d19749, d129684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19841 q = 1) (hb : d129752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19841, d129752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19841, d129752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19842 q = 1) (hb : d129753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19842, d129753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19842, d129753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19843 q = 1) (hb : d129754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19843, d129754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19843, d129754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19844 q = 1) (hb : d129755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19844, d129755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19844, d129755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19845 q = 1) (hb : d129756 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19845, d129756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19845, d129756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45087 (p : Pattern) (ha : d19809 p = 1) (hb : d129732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h2 (q : Pattern) (ha : d19805 q = 1) (hb : d129728 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19805, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19806 q = 1) (hb : d129729 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h5 (q : Pattern) (ha : d19765 q = 1) (hb : d129700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19766 q = 1) (hb : d129701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19807 q = 1) (hb : d129730 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19807, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19738 q = 1) (hb : d129673 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19738, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19738, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19739 q = 1) (hb : d129674 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19739, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19739, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19767 q = 1) (hb : d129702 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19767, d129702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19767, d129702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19808 q = 1) (hb : d129731 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19808, d129731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19808, d129731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9333 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9393 q = 1) (hb : d101026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d19809 q = 1) (hb : d129732 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19809, d129732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19809, d129732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro45088 (p : Pattern) (ha : d19815 p = 1) (hb : d129738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19810 q = 1) (hb : d129733 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19810, d129733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45087 q ha hb
    | true =>
      simp only [d19810, d129733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19811 q = 1) (hb : d129734 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19811, d129734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19811, d129734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19770 q = 1) (hb : d129705 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d129705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45082 q ha hb
    | true =>
      simp only [d19770, d129705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19771 q = 1) (hb : d129706 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d129706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d129706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19812 q = 1) (hb : d129735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19812, d129735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19812, d129735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19813 q = 1) (hb : d129736 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19813, d129736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19813, d129736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19814 q = 1) (hb : d129737 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19814, d129737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19814, d129737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19815 q = 1) (hb : d129738 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19815, d129738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19815, d129738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45089 (p : Pattern) (ha : d19833 p = 1) (hb : d129744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19770 q = 1) (hb : d129705 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19770, d129705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45082 q ha hb
    | true =>
      simp only [d19770, d129705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19771 q = 1) (hb : d129706 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19771, d129706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19771, d129706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19830 q = 1) (hb : d129741 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19830, d129741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19830, d129741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19831 q = 1) (hb : d129742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19831, d129742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19831, d129742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19832 q = 1) (hb : d129743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19832, d129743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19832, d129743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19833 q = 1) (hb : d129744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19833, d129744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19833, d129744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45090 (p : Pattern) (ha : d129750 p = 1) (hb : d130231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19816 q = 1) (hb : d129739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19816, d129739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45088 q ha hb
    | true =>
      simp only [d19816, d129739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45083 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129711 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129740 q = 1) (hb : d130227 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129740, d130227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129740, d130227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19834 q = 1) (hb : d129745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19834, d129745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45089 q ha hb
    | true =>
      simp only [d19834, d129745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19835 q = 1) (hb : d129746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19835, d129746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19835, d129746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129747 q = 1) (hb : d130228 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129747, d130228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129747, d130228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d129748 q = 1) (hb : d130229 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129748, d130229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129748, d130229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129749 q = 1) (hb : d130230 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129749, d130230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129749, d130230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129750 q = 1) (hb : d130231 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129750, d130231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129750, d130231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro45091 (p : Pattern) (ha : d129762 p = 1) (hb : d130237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129751 q = 1) (hb : d130232 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129751, d130232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129751, d130232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45090 q ha hb
  have h2 (q : Pattern) (ha : d19846 q = 1) (hb : d129757 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d129757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d129757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45086 q ha hb
  have h3 (q : Pattern) (ha : d129758 q = 1) (hb : d130233 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129758, d130233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129758, d130233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129759 q = 1) (hb : d130234 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129759, d130234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129759, d130234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129760 q = 1) (hb : d130235 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129760, d130235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129760, d130235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129761 q = 1) (hb : d130236 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129761, d130236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129761, d130236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129762 q = 1) (hb : d130237 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129762, d130237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129762, d130237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45092 (p : Pattern) (ha : d129768 p = 1) (hb : d130243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19761 q = 1) (hb : d129696 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d19761, d129696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19761, d129696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45081 q ha hb
  have h2 (q : Pattern) (ha : d19762 q = 1) (hb : d129697 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d19762, d129697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19762, d129697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19763 q = 1) (hb : d129698 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d19763, d129698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19763, d129698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19764 q = 1) (hb : d129699 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d19764, d129699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19764, d129699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129723 q = 1) (hb : d130222 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129723, d130222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129723, d130222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45085 q ha hb
  have h6 (q : Pattern) (ha : d129724 q = 1) (hb : d130223 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129724, d130223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129724, d130223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129725 q = 1) (hb : d130224 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129725, d130224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129725, d130224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129726 q = 1) (hb : d130225 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129726, d130225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129726, d130225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129727 q = 1) (hb : d130226 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129727, d130226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d129727, d130226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129763 q = 1) (hb : d130238 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129763, d130238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129763, d130238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45091 q ha hb
  have h11 (q : Pattern) (ha : d129764 q = 1) (hb : d130239 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129764, d130239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129764, d130239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129765 q = 1) (hb : d130240 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129765, d130240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129765, d130240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129766 q = 1) (hb : d130241 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129766, d130241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129766, d130241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129767 q = 1) (hb : d130242 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129767, d130242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129767, d130242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129768 q = 1) (hb : d130243 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129768, d130243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129768, d130243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro45093 (p : Pattern) (ha : d19877 p = 1) (hb : d129788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h2 (q : Pattern) (ha : d19765 q = 1) (hb : d129700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19766 q = 1) (hb : d129701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19867 q = 1) (hb : d129778 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19867, d129778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19867, d129778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19876 q = 1) (hb : d129787 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19876, d129787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19876, d129787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9487 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9496 q = 1) (hb : d101111 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19877 q = 1) (hb : d129788 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19877, d129788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19877, d129788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro45094 (p : Pattern) (ha : d19921 p = 1) (hb : d129799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19878 q = 1) (hb : d129789 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19878, d129789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45093 q ha hb
    | true =>
      simp only [d19878, d129789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19879 q = 1) (hb : d129790 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19879, d129790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19879, d129790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19918 q = 1) (hb : d129796 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19918, d129796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19918, d129796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19919 q = 1) (hb : d129797 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19919, d129797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19919, d129797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19920 q = 1) (hb : d129798 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19920, d129798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19920, d129798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19921 q = 1) (hb : d129799 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19921, d129799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19921, d129799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45095 (p : Pattern) (ha : d19927 p = 1) (hb : d129818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19922 q = 1) (hb : d129813 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19922, d129813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45094 q ha hb
    | true =>
      simp only [d19922, d129813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19923 q = 1) (hb : d129814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19923, d129814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19923, d129814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19924 q = 1) (hb : d129815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19924, d129815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19924, d129815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19925 q = 1) (hb : d129816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19925, d129816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19925, d129816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19926 q = 1) (hb : d129817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19926, d129817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19926, d129817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19927 q = 1) (hb : d129818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19927, d129818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19927, d129818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45096 (p : Pattern) (ha : d19864 p = 1) (hb : d129775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9475 q = 1) (hb : d101090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23274 q ha hb
    | true =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
  have h2 (q : Pattern) (ha : d19858 q = 1) (hb : d129769 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19858, d129769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19858, d129769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19859 q = 1) (hb : d129770 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19859, d129770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19859, d129770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9479 q = 1) (hb : d101094 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23275 q ha hb
  have h5 (q : Pattern) (ha : d19860 q = 1) (hb : d129771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19860, d129771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19860, d129771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19861 q = 1) (hb : d129772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19861, d129772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19861, d129772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19862 q = 1) (hb : d129773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19862, d129773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19862, d129773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h9 (q : Pattern) (ha : d19805 q = 1) (hb : d129728 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19805, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19806 q = 1) (hb : d129729 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h12 (q : Pattern) (ha : d19765 q = 1) (hb : d129700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19766 q = 1) (hb : d129701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19807 q = 1) (hb : d129730 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19807, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19863 q = 1) (hb : d129774 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19863, d129774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19863, d129774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9476 q = 1) (hb : d101091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d9477 q = 1) (hb : d101092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9480 q = 1) (hb : d101095 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9481 q = 1) (hb : d101096 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9482 q = 1) (hb : d101097 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9483 q = 1) (hb : d101098 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d19864 q = 1) (hb : d129775 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19864, d129775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19864, d129775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro45097 (p : Pattern) (ha : d19869 p = 1) (hb : d129780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h2 (q : Pattern) (ha : d19805 q = 1) (hb : d129728 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19805, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19805, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19806 q = 1) (hb : d129729 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19806, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19806, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h5 (q : Pattern) (ha : d19765 q = 1) (hb : d129700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19765, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19765, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19766 q = 1) (hb : d129701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19766, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19766, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19807 q = 1) (hb : d129730 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19807, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19807, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19867 q = 1) (hb : d129778 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19867, d129778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19867, d129778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19868 q = 1) (hb : d129779 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19868, d129779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19868, d129779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9487 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9488 q = 1) (hb : d101103 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19869 q = 1) (hb : d129780 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19869, d129780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19869, d129780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45098 (p : Pattern) (ha : d19875 p = 1) (hb : d129786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19865 q = 1) (hb : d129776 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19865, d129776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45096 q ha hb
    | true =>
      simp only [d19865, d129776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19866 q = 1) (hb : d129777 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19866, d129777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19866, d129777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19870 q = 1) (hb : d129781 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d129781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45097 q ha hb
    | true =>
      simp only [d19870, d129781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19871 q = 1) (hb : d129782 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d129782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d129782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19872 q = 1) (hb : d129783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19872, d129783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19872, d129783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19873 q = 1) (hb : d129784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19873, d129784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19873, d129784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19874 q = 1) (hb : d129785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19874, d129785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19874, d129785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19875 q = 1) (hb : d129786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19875, d129786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19875, d129786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45099 (p : Pattern) (ha : d19883 p = 1) (hb : d129794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19870 q = 1) (hb : d129781 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d129781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45097 q ha hb
    | true =>
      simp only [d19870, d129781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19871 q = 1) (hb : d129782 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d129782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d129782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19878 q = 1) (hb : d129789 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19878, d129789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45093 q ha hb
    | true =>
      simp only [d19878, d129789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19879 q = 1) (hb : d129790 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19879, d129790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19879, d129790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19880 q = 1) (hb : d129791 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19880, d129791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19880, d129791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19881 q = 1) (hb : d129792 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19881, d129792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19881, d129792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19882 q = 1) (hb : d129793 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19882, d129793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19882, d129793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19883 q = 1) (hb : d129794 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19883, d129794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19883, d129794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45100 (p : Pattern) (ha : d19910 p = 1) (hb : d129805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19870 q = 1) (hb : d129781 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19870, d129781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45097 q ha hb
    | true =>
      simp only [d19870, d129781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19871 q = 1) (hb : d129782 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19871, d129782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19871, d129782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19907 q = 1) (hb : d129802 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19907, d129802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19907, d129802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19908 q = 1) (hb : d129803 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19908, d129803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19908, d129803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19909 q = 1) (hb : d129804 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19909, d129804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19909, d129804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19910 q = 1) (hb : d129805 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19910, d129805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19910, d129805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45101 (p : Pattern) (ha : d129811 p = 1) (hb : d130248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19884 q = 1) (hb : d129795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19884, d129795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45098 q ha hb
    | true =>
      simp only [d19884, d129795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45099 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129801 q = 1) (hb : d130244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129801, d130244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129801, d130244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d19911 q = 1) (hb : d129806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19911, d129806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45100 q ha hb
    | true =>
      simp only [d19911, d129806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19912 q = 1) (hb : d129807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19912, d129807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19912, d129807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129808 q = 1) (hb : d130245 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129808, d130245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129808, d130245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d129809 q = 1) (hb : d130246 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129809, d130246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129809, d130246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129810 q = 1) (hb : d130247 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129810, d130247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129810, d130247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129811 q = 1) (hb : d130248 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129811, d130248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129811, d130248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro45102 (p : Pattern) (ha : d129824 p = 1) (hb : d130254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129812 q = 1) (hb : d130249 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129812, d130249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129812, d130249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45101 q ha hb
  have h2 (q : Pattern) (ha : d19928 q = 1) (hb : d129819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19928, d129819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19928, d129819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45095 q ha hb
  have h3 (q : Pattern) (ha : d129820 q = 1) (hb : d130250 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129820, d130250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129820, d130250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129821 q = 1) (hb : d130251 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129821, d130251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129821, d130251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129822 q = 1) (hb : d130252 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129822, d130252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129822, d130252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129823 q = 1) (hb : d130253 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129823, d130253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129823, d130253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129824 q = 1) (hb : d130254 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129824, d130254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129824, d130254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45103 (p : Pattern) (ha : d129830 p = 1) (hb : d130260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129825 q = 1) (hb : d130255 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129825, d130255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129825, d130255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45102 q ha hb
  have h2 (q : Pattern) (ha : d129826 q = 1) (hb : d130256 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129826, d130256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129826, d130256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129827 q = 1) (hb : d130257 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129827, d130257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129827, d130257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129828 q = 1) (hb : d130258 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129828, d130258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129828, d130258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129829 q = 1) (hb : d130259 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129829, d130259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129829, d130259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129830 q = 1) (hb : d130260 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129830, d130260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129830, d130260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45104 (p : Pattern) (ha : d19965 p = 1) (hb : d129856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h2 (q : Pattern) (ha : d19948 q = 1) (hb : d129839 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19948, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19949 q = 1) (hb : d129840 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19955 q = 1) (hb : d129846 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19955, d129846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19955, d129846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19964 q = 1) (hb : d129855 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19964, d129855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19964, d129855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9632 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9641 q = 1) (hb : d101221 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d19965 q = 1) (hb : d129856 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19965, d129856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19965, d129856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro45105 (p : Pattern) (ha : d20011 p = 1) (hb : d129867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19966 q = 1) (hb : d129857 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19966, d129857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45104 q ha hb
    | true =>
      simp only [d19966, d129857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19967 q = 1) (hb : d129858 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19967, d129858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19967, d129858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20008 q = 1) (hb : d129864 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20008, d129864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20008, d129864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20009 q = 1) (hb : d129865 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20009, d129865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20009, d129865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20010 q = 1) (hb : d129866 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20010, d129866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20010, d129866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20011 q = 1) (hb : d129867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20011, d129867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20011, d129867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45106 (p : Pattern) (ha : d20017 p = 1) (hb : d129886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20012 q = 1) (hb : d129881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20012, d129881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45105 q ha hb
    | true =>
      simp only [d20012, d129881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20013 q = 1) (hb : d129882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20013, d129882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20013, d129882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20014 q = 1) (hb : d129883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20014, d129883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20014, d129883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20015 q = 1) (hb : d129884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20015, d129884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20015, d129884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20016 q = 1) (hb : d129885 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20016, d129885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20016, d129885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20017 q = 1) (hb : d129886 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20017, d129886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20017, d129886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45107 (p : Pattern) (ha : d19952 p = 1) (hb : d129843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9609 q = 1) (hb : d101189 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23292 q ha hb
    | true =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
  have h2 (q : Pattern) (ha : d19941 q = 1) (hb : d129832 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19941, d129832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19941, d129832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19942 q = 1) (hb : d129833 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19942, d129833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19942, d129833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9614 q = 1) (hb : d101194 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23294 q ha hb
  have h5 (q : Pattern) (ha : d19943 q = 1) (hb : d129834 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19943, d129834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19943, d129834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19944 q = 1) (hb : d129835 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19944, d129835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19944, d129835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19945 q = 1) (hb : d129836 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19945, d129836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19945, d129836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h9 (q : Pattern) (ha : d19946 q = 1) (hb : d129837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19946, d129837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19946, d129837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19947 q = 1) (hb : d129838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19947, d129838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19947, d129838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h12 (q : Pattern) (ha : d19948 q = 1) (hb : d129839 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19948, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19949 q = 1) (hb : d129840 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19950 q = 1) (hb : d129841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19950, d129841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19950, d129841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19951 q = 1) (hb : d129842 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19951, d129842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19951, d129842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9610 q = 1) (hb : d101190 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d9611 q = 1) (hb : d101191 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9615 q = 1) (hb : d101195 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9616 q = 1) (hb : d101196 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9617 q = 1) (hb : d101197 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9621 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9622 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9627 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9628 q = 1) (hb : d101208 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d19952 q = 1) (hb : d129843 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19952, d129843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19952, d129843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro45108 (p : Pattern) (ha : d19957 p = 1) (hb : d129848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h2 (q : Pattern) (ha : d19946 q = 1) (hb : d129837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19946, d129837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19946, d129837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19947 q = 1) (hb : d129838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19947, d129838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19947, d129838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h5 (q : Pattern) (ha : d19948 q = 1) (hb : d129839 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19948, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19948, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19949 q = 1) (hb : d129840 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19949, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19949, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19950 q = 1) (hb : d129841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19950, d129841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19950, d129841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19955 q = 1) (hb : d129846 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19955, d129846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19955, d129846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19956 q = 1) (hb : d129847 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19956, d129847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19956, d129847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9621 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9622 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9627 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9632 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9633 q = 1) (hb : d101213 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19957 q = 1) (hb : d129848 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19957, d129848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19957, d129848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45109 (p : Pattern) (ha : d19963 p = 1) (hb : d129854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19953 q = 1) (hb : d129844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19953, d129844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45107 q ha hb
    | true =>
      simp only [d19953, d129844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19954 q = 1) (hb : d129845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19954, d129845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19954, d129845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19958 q = 1) (hb : d129849 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d129849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45108 q ha hb
    | true =>
      simp only [d19958, d129849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19959 q = 1) (hb : d129850 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d129850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d129850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19960 q = 1) (hb : d129851 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19960, d129851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19960, d129851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19961 q = 1) (hb : d129852 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19961, d129852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19961, d129852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19962 q = 1) (hb : d129853 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19962, d129853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19962, d129853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19963 q = 1) (hb : d129854 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19963, d129854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19963, d129854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45110 (p : Pattern) (ha : d19971 p = 1) (hb : d129862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19958 q = 1) (hb : d129849 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d129849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45108 q ha hb
    | true =>
      simp only [d19958, d129849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19959 q = 1) (hb : d129850 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d129850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d129850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19966 q = 1) (hb : d129857 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19966, d129857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45104 q ha hb
    | true =>
      simp only [d19966, d129857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19967 q = 1) (hb : d129858 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19967, d129858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19967, d129858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19968 q = 1) (hb : d129859 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19968, d129859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19968, d129859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19969 q = 1) (hb : d129860 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19969, d129860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19969, d129860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19970 q = 1) (hb : d129861 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19970, d129861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19970, d129861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19971 q = 1) (hb : d129862 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19971, d129862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19971, d129862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45111 (p : Pattern) (ha : d20000 p = 1) (hb : d129873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19958 q = 1) (hb : d129849 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19958, d129849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45108 q ha hb
    | true =>
      simp only [d19958, d129849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19959 q = 1) (hb : d129850 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19959, d129850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19959, d129850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19997 q = 1) (hb : d129870 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19997, d129870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19997, d129870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19998 q = 1) (hb : d129871 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19998, d129871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19998, d129871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19999 q = 1) (hb : d129872 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19999, d129872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19999, d129872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20000 q = 1) (hb : d129873 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20000, d129873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20000, d129873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45112 (p : Pattern) (ha : d129879 p = 1) (hb : d130266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19972 q = 1) (hb : d129863 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19972, d129863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45109 q ha hb
    | true =>
      simp only [d19972, d129863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45110 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129868 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129869 q = 1) (hb : d130262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129869, d130262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129869, d130262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20001 q = 1) (hb : d129874 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20001, d129874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45111 q ha hb
    | true =>
      simp only [d20001, d129874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20002 q = 1) (hb : d129875 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20002, d129875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20002, d129875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129876 q = 1) (hb : d130263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129876, d130263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129876, d130263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d129877 q = 1) (hb : d130264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129877, d130264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129877, d130264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129878 q = 1) (hb : d130265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129878, d130265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129878, d130265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129879 q = 1) (hb : d130266 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129879, d130266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129879, d130266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro45113 (p : Pattern) (ha : d129892 p = 1) (hb : d130272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129880 q = 1) (hb : d130267 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129880, d130267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129880, d130267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45112 q ha hb
  have h2 (q : Pattern) (ha : d20018 q = 1) (hb : d129887 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20018, d129887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20018, d129887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45106 q ha hb
  have h3 (q : Pattern) (ha : d129888 q = 1) (hb : d130268 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129888, d130268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129888, d130268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129889 q = 1) (hb : d130269 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129889, d130269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129889, d130269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129890 q = 1) (hb : d130270 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129890, d130270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129890, d130270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129891 q = 1) (hb : d130271 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129891, d130271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129891, d130271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129892 q = 1) (hb : d130272 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129892, d130272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129892, d130272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45114 (p : Pattern) (ha : d129898 p = 1) (hb : d130278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129893 q = 1) (hb : d130273 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129893, d130273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129893, d130273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45113 q ha hb
  have h2 (q : Pattern) (ha : d129894 q = 1) (hb : d130274 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129894, d130274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129894, d130274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129895 q = 1) (hb : d130275 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129895, d130275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129895, d130275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129896 q = 1) (hb : d130276 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129896, d130276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129896, d130276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129897 q = 1) (hb : d130277 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129897, d130277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129897, d130277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129898 q = 1) (hb : d130278 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129898, d130278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129898, d130278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45115 (p : Pattern) (ha : d20059 p = 1) (hb : d129928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h2 (q : Pattern) (ha : d20055 q = 1) (hb : d129924 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20055, d129924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20055, d129924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20056 q = 1) (hb : d129925 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20056, d129925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20056, d129925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20057 q = 1) (hb : d129926 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20057, d129926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20057, d129926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20058 q = 1) (hb : d129927 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20058, d129927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20058, d129927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9871 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9872 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9873 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9874 q = 1) (hb : d101395 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d20059 q = 1) (hb : d129928 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20059, d129928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20059, d129928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro45116 (p : Pattern) (ha : d20114 p = 1) (hb : d129947 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20060 q = 1) (hb : d129929 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d129929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45115 q ha hb
    | true =>
      simp only [d20060, d129929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20061 q = 1) (hb : d129930 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d129930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d129930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20111 q = 1) (hb : d129944 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20111, d129944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20111, d129944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20112 q = 1) (hb : d129945 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20112, d129945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20112, d129945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20113 q = 1) (hb : d129946 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20113, d129946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20113, d129946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20114 q = 1) (hb : d129947 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20114, d129947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20114, d129947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45117 (p : Pattern) (ha : d20120 p = 1) (hb : d129973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20115 q = 1) (hb : d129968 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20115, d129968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45116 q ha hb
    | true =>
      simp only [d20115, d129968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20116 q = 1) (hb : d129969 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20116, d129969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20116, d129969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20117 q = 1) (hb : d129970 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20117, d129970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20117, d129970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20118 q = 1) (hb : d129971 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20118, d129971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20118, d129971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20119 q = 1) (hb : d129972 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20119, d129972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20119, d129972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20120 q = 1) (hb : d129973 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20120, d129973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20120, d129973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45118 (p : Pattern) (ha : d20043 p = 1) (hb : d129912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9807 q = 1) (hb : d101328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23314 q ha hb
    | true =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
  have h2 (q : Pattern) (ha : d20032 q = 1) (hb : d129901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20032, d129901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20032, d129901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20033 q = 1) (hb : d129902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20033, d129902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20033, d129902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9822 q = 1) (hb : d101343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23318 q ha hb
  have h5 (q : Pattern) (ha : d20034 q = 1) (hb : d129903 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20034, d129903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20034, d129903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20035 q = 1) (hb : d129904 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20035, d129904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20035, d129904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20036 q = 1) (hb : d129905 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20036, d129905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20036, d129905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h9 (q : Pattern) (ha : d20037 q = 1) (hb : d129906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20037, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20038 q = 1) (hb : d129907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h12 (q : Pattern) (ha : d20039 q = 1) (hb : d129908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20039, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20040 q = 1) (hb : d129909 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20041 q = 1) (hb : d129910 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20041, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d20042 q = 1) (hb : d129911 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20042, d129911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20042, d129911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9808 q = 1) (hb : d101329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d9809 q = 1) (hb : d101330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9823 q = 1) (hb : d101344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9824 q = 1) (hb : d101345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9825 q = 1) (hb : d101346 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9855 q = 1) (hb : d101376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d20043 q = 1) (hb : d129912 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20043, d129912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20043, d129912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro45119 (p : Pattern) (ha : d20048 p = 1) (hb : d129917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h2 (q : Pattern) (ha : d20037 q = 1) (hb : d129906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20037, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20038 q = 1) (hb : d129907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h5 (q : Pattern) (ha : d20039 q = 1) (hb : d129908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20039, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20040 q = 1) (hb : d129909 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20041 q = 1) (hb : d129910 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20041, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20046 q = 1) (hb : d129915 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20046, d129915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20046, d129915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20047 q = 1) (hb : d129916 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20047, d129916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20047, d129916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9859 q = 1) (hb : d101380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9860 q = 1) (hb : d101381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20048 q = 1) (hb : d129917 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20048, d129917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20048, d129917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45120 (p : Pattern) (ha : d20054 p = 1) (hb : d129923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20044 q = 1) (hb : d129913 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20044, d129913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45118 q ha hb
    | true =>
      simp only [d20044, d129913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20045 q = 1) (hb : d129914 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20045, d129914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20045, d129914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20049 q = 1) (hb : d129918 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20049, d129918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45119 q ha hb
    | true =>
      simp only [d20049, d129918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20050 q = 1) (hb : d129919 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20050, d129919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20050, d129919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20051 q = 1) (hb : d129920 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20051, d129920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20051, d129920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20052 q = 1) (hb : d129921 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20052, d129921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20052, d129921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20053 q = 1) (hb : d129922 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20053, d129922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20053, d129922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20054 q = 1) (hb : d129923 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20054, d129923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20054, d129923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45121 (p : Pattern) (ha : d20065 p = 1) (hb : d129934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20049 q = 1) (hb : d129918 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20049, d129918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45119 q ha hb
    | true =>
      simp only [d20049, d129918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20050 q = 1) (hb : d129919 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20050, d129919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20050, d129919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20060 q = 1) (hb : d129929 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d129929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45115 q ha hb
    | true =>
      simp only [d20060, d129929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20061 q = 1) (hb : d129930 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d129930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d129930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20062 q = 1) (hb : d129931 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20062, d129931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20062, d129931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20063 q = 1) (hb : d129932 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20063, d129932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20063, d129932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20064 q = 1) (hb : d129933 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20064, d129933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20064, d129933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20065 q = 1) (hb : d129934 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20065, d129934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20065, d129934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45122 (p : Pattern) (ha : d20097 p = 1) (hb : d129954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h2 (q : Pattern) (ha : d20037 q = 1) (hb : d129906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20037, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20038 q = 1) (hb : d129907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h5 (q : Pattern) (ha : d20039 q = 1) (hb : d129908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20039, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20040 q = 1) (hb : d129909 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20041 q = 1) (hb : d129910 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20041, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9988 q = 1) (hb : d101419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23324 q ha hb
  have h9 (q : Pattern) (ha : d20093 q = 1) (hb : d129950 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20093, d129950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20093, d129950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20094 q = 1) (hb : d129951 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20094, d129951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20094, d129951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20095 q = 1) (hb : d129952 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20095, d129952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20095, d129952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d20096 q = 1) (hb : d129953 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20096, d129953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20096, d129953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9989 q = 1) (hb : d101420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9990 q = 1) (hb : d101421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9991 q = 1) (hb : d101422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9992 q = 1) (hb : d101423 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d20097 q = 1) (hb : d129954 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20097, d129954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20097, d129954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro45123 (p : Pattern) (ha : d20103 p = 1) (hb : d129960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20098 q = 1) (hb : d129955 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20098, d129955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45122 q ha hb
    | true =>
      simp only [d20098, d129955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20099 q = 1) (hb : d129956 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20099, d129956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20099, d129956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20100 q = 1) (hb : d129957 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20100, d129957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20100, d129957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20101 q = 1) (hb : d129958 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20101, d129958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20101, d129958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20102 q = 1) (hb : d129959 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20102, d129959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20102, d129959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20103 q = 1) (hb : d129960 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20103, d129960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20103, d129960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45124 (p : Pattern) (ha : d129966 p = 1) (hb : d130285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20066 q = 1) (hb : d129935 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20066, d129935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45120 q ha hb
    | true =>
      simp only [d20066, d129935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45121 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129948 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129949 q = 1) (hb : d130281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129949, d130281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129949, d130281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20104 q = 1) (hb : d129961 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20104, d129961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45123 q ha hb
    | true =>
      simp only [d20104, d129961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20105 q = 1) (hb : d129962 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20105, d129962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20105, d129962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129963 q = 1) (hb : d130282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129963, d130282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129963, d130282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d129964 q = 1) (hb : d130283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129964, d130283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129964, d130283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129965 q = 1) (hb : d130284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129965, d130284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129965, d130284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129966 q = 1) (hb : d130285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129966, d130285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129966, d130285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro45125 (p : Pattern) (ha : d129979 p = 1) (hb : d130291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129967 q = 1) (hb : d130286 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129967, d130286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129967, d130286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45124 q ha hb
  have h2 (q : Pattern) (ha : d20121 q = 1) (hb : d129974 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20121, d129974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20121, d129974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45117 q ha hb
  have h3 (q : Pattern) (ha : d129975 q = 1) (hb : d130287 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129975, d130287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129975, d130287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129976 q = 1) (hb : d130288 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129976, d130288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129976, d130288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129977 q = 1) (hb : d130289 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129977, d130289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129977, d130289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129978 q = 1) (hb : d130290 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129978, d130290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129978, d130290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129979 q = 1) (hb : d130291 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129979, d130291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129979, d130291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45126 (p : Pattern) (ha : d129985 p = 1) (hb : d130297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129980 q = 1) (hb : d130292 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129980, d130292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129980, d130292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45125 q ha hb
  have h2 (q : Pattern) (ha : d129981 q = 1) (hb : d130293 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129981, d130293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129981, d130293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129982 q = 1) (hb : d130294 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129982, d130294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129982, d130294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129983 q = 1) (hb : d130295 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129983, d130295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129983, d130295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129984 q = 1) (hb : d130296 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129984, d130296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129984, d130296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129985 q = 1) (hb : d130297 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129985, d130297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129985, d130297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45127 (p : Pattern) (ha : d20163 p = 1) (hb : d130016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h2 (q : Pattern) (ha : d20159 q = 1) (hb : d130012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20159, d130012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20159, d130012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20160 q = 1) (hb : d130013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20160, d130013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20160, d130013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20161 q = 1) (hb : d130014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20161, d130014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20161, d130014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20162 q = 1) (hb : d130015 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20162, d130015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20162, d130015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10165 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10166 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10167 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10168 q = 1) (hb : d101595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d20163 q = 1) (hb : d130016 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20163, d130016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20163, d130016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro45128 (p : Pattern) (ha : d20218 p = 1) (hb : d130035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20164 q = 1) (hb : d130017 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d130017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45127 q ha hb
    | true =>
      simp only [d20164, d130017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20165 q = 1) (hb : d130018 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d130018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d130018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20215 q = 1) (hb : d130032 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20215, d130032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20215, d130032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20216 q = 1) (hb : d130033 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20216, d130033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20216, d130033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20217 q = 1) (hb : d130034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20217, d130034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20217, d130034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20218 q = 1) (hb : d130035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20218, d130035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20218, d130035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45129 (p : Pattern) (ha : d20224 p = 1) (hb : d130061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20219 q = 1) (hb : d130056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20219, d130056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45128 q ha hb
    | true =>
      simp only [d20219, d130056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20220 q = 1) (hb : d130057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20220, d130057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20220, d130057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20221 q = 1) (hb : d130058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20221, d130058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20221, d130058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20222 q = 1) (hb : d130059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20222, d130059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20222, d130059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20223 q = 1) (hb : d130060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20223, d130060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20223, d130060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20224 q = 1) (hb : d130061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20224, d130061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20224, d130061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45130 (p : Pattern) (ha : d20147 p = 1) (hb : d130000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10092 q = 1) (hb : d101519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23342 q ha hb
    | true =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
  have h2 (q : Pattern) (ha : d20136 q = 1) (hb : d129989 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20136, d129989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20136, d129989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20137 q = 1) (hb : d129990 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20137, d129990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20137, d129990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10107 q = 1) (hb : d101534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23346 q ha hb
  have h5 (q : Pattern) (ha : d20138 q = 1) (hb : d129991 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20138, d129991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20138, d129991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20139 q = 1) (hb : d129992 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20139, d129992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20139, d129992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20140 q = 1) (hb : d129993 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20140, d129993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20140, d129993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h9 (q : Pattern) (ha : d20141 q = 1) (hb : d129994 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20142 q = 1) (hb : d129995 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h12 (q : Pattern) (ha : d20143 q = 1) (hb : d129996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20144 q = 1) (hb : d129997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20145 q = 1) (hb : d129998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d20146 q = 1) (hb : d129999 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20146, d129999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20146, d129999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10093 q = 1) (hb : d101520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d10094 q = 1) (hb : d101521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10108 q = 1) (hb : d101535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10109 q = 1) (hb : d101536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10110 q = 1) (hb : d101537 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10146 q = 1) (hb : d101573 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d20147 q = 1) (hb : d130000 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20147, d130000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20147, d130000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro45131 (p : Pattern) (ha : d20152 p = 1) (hb : d130005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h2 (q : Pattern) (ha : d20141 q = 1) (hb : d129994 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20142 q = 1) (hb : d129995 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h5 (q : Pattern) (ha : d20143 q = 1) (hb : d129996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20144 q = 1) (hb : d129997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20145 q = 1) (hb : d129998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20150 q = 1) (hb : d130003 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20150, d130003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20150, d130003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20151 q = 1) (hb : d130004 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20151, d130004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20151, d130004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10150 q = 1) (hb : d101577 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10151 q = 1) (hb : d101578 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20152 q = 1) (hb : d130005 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20152, d130005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20152, d130005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45132 (p : Pattern) (ha : d20158 p = 1) (hb : d130011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20148 q = 1) (hb : d130001 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20148, d130001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45130 q ha hb
    | true =>
      simp only [d20148, d130001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20149 q = 1) (hb : d130002 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20149, d130002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20149, d130002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20153 q = 1) (hb : d130006 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20153, d130006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45131 q ha hb
    | true =>
      simp only [d20153, d130006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20154 q = 1) (hb : d130007 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20154, d130007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20154, d130007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20155 q = 1) (hb : d130008 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20155, d130008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20155, d130008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20156 q = 1) (hb : d130009 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20156, d130009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20156, d130009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20157 q = 1) (hb : d130010 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20157, d130010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20157, d130010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20158 q = 1) (hb : d130011 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20158, d130011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20158, d130011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45133 (p : Pattern) (ha : d20169 p = 1) (hb : d130022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20153 q = 1) (hb : d130006 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20153, d130006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45131 q ha hb
    | true =>
      simp only [d20153, d130006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20154 q = 1) (hb : d130007 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20154, d130007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20154, d130007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20164 q = 1) (hb : d130017 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d130017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45127 q ha hb
    | true =>
      simp only [d20164, d130017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20165 q = 1) (hb : d130018 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d130018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d130018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20166 q = 1) (hb : d130019 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20166, d130019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20166, d130019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20167 q = 1) (hb : d130020 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20167, d130020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20167, d130020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20168 q = 1) (hb : d130021 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20168, d130021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20168, d130021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20169 q = 1) (hb : d130022 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20169, d130022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20169, d130022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45134 (p : Pattern) (ha : d20201 p = 1) (hb : d130042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h2 (q : Pattern) (ha : d20141 q = 1) (hb : d129994 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20142 q = 1) (hb : d129995 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h5 (q : Pattern) (ha : d20143 q = 1) (hb : d129996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20144 q = 1) (hb : d129997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20145 q = 1) (hb : d129998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10294 q = 1) (hb : d101619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23352 q ha hb
  have h9 (q : Pattern) (ha : d20197 q = 1) (hb : d130038 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20197, d130038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20197, d130038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20198 q = 1) (hb : d130039 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20198, d130039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20198, d130039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20199 q = 1) (hb : d130040 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20199, d130040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20199, d130040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d20200 q = 1) (hb : d130041 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20200, d130041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20200, d130041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10295 q = 1) (hb : d101620 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10296 q = 1) (hb : d101621 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10297 q = 1) (hb : d101622 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10298 q = 1) (hb : d101623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d20201 q = 1) (hb : d130042 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20201, d130042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20201, d130042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro45135 (p : Pattern) (ha : d20207 p = 1) (hb : d130048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20202 q = 1) (hb : d130043 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20202, d130043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45134 q ha hb
    | true =>
      simp only [d20202, d130043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20203 q = 1) (hb : d130044 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20203, d130044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20203, d130044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20204 q = 1) (hb : d130045 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20204, d130045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20204, d130045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20205 q = 1) (hb : d130046 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20205, d130046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20205, d130046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20206 q = 1) (hb : d130047 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20206, d130047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20206, d130047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20207 q = 1) (hb : d130048 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20207, d130048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20207, d130048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45136 (p : Pattern) (ha : d130054 p = 1) (hb : d130305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20170 q = 1) (hb : d130023 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20170, d130023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45132 q ha hb
    | true =>
      simp only [d20170, d130023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45133 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130037 q = 1) (hb : d130301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130037, d130301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130037, d130301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20208 q = 1) (hb : d130049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20208, d130049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45135 q ha hb
    | true =>
      simp only [d20208, d130049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20209 q = 1) (hb : d130050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20209, d130050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20209, d130050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130051 q = 1) (hb : d130302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130051, d130302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130051, d130302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d130052 q = 1) (hb : d130303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130052, d130303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130052, d130303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130053 q = 1) (hb : d130304 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130053, d130304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130053, d130304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130054 q = 1) (hb : d130305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130054, d130305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130054, d130305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro45137 (p : Pattern) (ha : d130067 p = 1) (hb : d130311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130055 q = 1) (hb : d130306 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130055, d130306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130055, d130306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45136 q ha hb
  have h2 (q : Pattern) (ha : d20225 q = 1) (hb : d130062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20225, d130062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20225, d130062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45129 q ha hb
  have h3 (q : Pattern) (ha : d130063 q = 1) (hb : d130307 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130063, d130307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130063, d130307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130064 q = 1) (hb : d130308 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130064, d130308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130064, d130308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130065 q = 1) (hb : d130309 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130065, d130309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130065, d130309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130066 q = 1) (hb : d130310 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130066, d130310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130066, d130310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130067 q = 1) (hb : d130311 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130067, d130311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130067, d130311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45138 (p : Pattern) (ha : d130073 p = 1) (hb : d130317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130068 q = 1) (hb : d130312 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130068, d130312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130068, d130312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45137 q ha hb
  have h2 (q : Pattern) (ha : d130069 q = 1) (hb : d130313 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130069, d130313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130069, d130313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130070 q = 1) (hb : d130314 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130070, d130314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130070, d130314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130071 q = 1) (hb : d130315 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130071, d130315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130071, d130315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130072 q = 1) (hb : d130316 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130072, d130316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130072, d130316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130073 q = 1) (hb : d130317 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130073, d130317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130073, d130317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45139 (p : Pattern) (ha : d20268 p = 1) (hb : d130105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h2 (q : Pattern) (ha : d20264 q = 1) (hb : d130101 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20264, d130101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20264, d130101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20265 q = 1) (hb : d130102 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20265, d130102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20265, d130102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20266 q = 1) (hb : d130103 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20266, d130103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20266, d130103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20267 q = 1) (hb : d130104 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20267, d130104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20267, d130104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10442 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10443 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10444 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10445 q = 1) (hb : d101766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d20268 q = 1) (hb : d130105 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20268, d130105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20268, d130105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro45140 (p : Pattern) (ha : d20323 p = 1) (hb : d130124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20269 q = 1) (hb : d130106 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d130106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45139 q ha hb
    | true =>
      simp only [d20269, d130106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20270 q = 1) (hb : d130107 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d130107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d130107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20320 q = 1) (hb : d130121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20320, d130121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20320, d130121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20321 q = 1) (hb : d130122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20321, d130122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20321, d130122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20322 q = 1) (hb : d130123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20322, d130123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20322, d130123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20323 q = 1) (hb : d130124 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20323, d130124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20323, d130124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45141 (p : Pattern) (ha : d20329 p = 1) (hb : d130150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20324 q = 1) (hb : d130145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20324, d130145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45140 q ha hb
    | true =>
      simp only [d20324, d130145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20325 q = 1) (hb : d130146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20325, d130146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20325, d130146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20326 q = 1) (hb : d130147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20326, d130147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20326, d130147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20327 q = 1) (hb : d130148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20327, d130148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20327, d130148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20328 q = 1) (hb : d130149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20328, d130149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20328, d130149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20329 q = 1) (hb : d130150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20329, d130150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20329, d130150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45142 (p : Pattern) (ha : d20252 p = 1) (hb : d130089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10378 q = 1) (hb : d101699 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23368 q ha hb
    | true =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
  have h2 (q : Pattern) (ha : d20241 q = 1) (hb : d130078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20241, d130078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20241, d130078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20242 q = 1) (hb : d130079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20242, d130079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20242, d130079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10383 q = 1) (hb : d101704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23371 q ha hb
  have h5 (q : Pattern) (ha : d20243 q = 1) (hb : d130080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20243, d130080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20243, d130080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20244 q = 1) (hb : d130081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20244, d130081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20244, d130081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20245 q = 1) (hb : d130082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20245, d130082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20245, d130082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h9 (q : Pattern) (ha : d20246 q = 1) (hb : d130083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20247 q = 1) (hb : d130084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h12 (q : Pattern) (ha : d20248 q = 1) (hb : d130085 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20249 q = 1) (hb : d130086 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20250 q = 1) (hb : d130087 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d20251 q = 1) (hb : d130088 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20251, d130088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20251, d130088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10379 q = 1) (hb : d101700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d10380 q = 1) (hb : d101701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10384 q = 1) (hb : d101705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10385 q = 1) (hb : d101706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10386 q = 1) (hb : d101707 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10423 q = 1) (hb : d101744 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d20252 q = 1) (hb : d130089 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20252, d130089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d20252, d130089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro45143 (p : Pattern) (ha : d20257 p = 1) (hb : d130094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h2 (q : Pattern) (ha : d20246 q = 1) (hb : d130083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20247 q = 1) (hb : d130084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h5 (q : Pattern) (ha : d20248 q = 1) (hb : d130085 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20249 q = 1) (hb : d130086 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20250 q = 1) (hb : d130087 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20255 q = 1) (hb : d130092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20255, d130092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20255, d130092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20256 q = 1) (hb : d130093 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20256, d130093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20256, d130093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10427 q = 1) (hb : d101748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10428 q = 1) (hb : d101749 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20257 q = 1) (hb : d130094 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20257, d130094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20257, d130094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro45144 (p : Pattern) (ha : d20263 p = 1) (hb : d130100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20253 q = 1) (hb : d130090 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20253, d130090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45142 q ha hb
    | true =>
      simp only [d20253, d130090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20254 q = 1) (hb : d130091 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20254, d130091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20254, d130091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20258 q = 1) (hb : d130095 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20258, d130095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45143 q ha hb
    | true =>
      simp only [d20258, d130095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20259 q = 1) (hb : d130096 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20259, d130096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20259, d130096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20260 q = 1) (hb : d130097 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20260, d130097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20260, d130097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20261 q = 1) (hb : d130098 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20261, d130098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20261, d130098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20262 q = 1) (hb : d130099 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20262, d130099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20262, d130099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20263 q = 1) (hb : d130100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20263, d130100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20263, d130100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45145 (p : Pattern) (ha : d20274 p = 1) (hb : d130111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20258 q = 1) (hb : d130095 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20258, d130095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45143 q ha hb
    | true =>
      simp only [d20258, d130095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20259 q = 1) (hb : d130096 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20259, d130096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20259, d130096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20269 q = 1) (hb : d130106 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d130106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45139 q ha hb
    | true =>
      simp only [d20269, d130106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20270 q = 1) (hb : d130107 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d130107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d130107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20271 q = 1) (hb : d130108 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20271, d130108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20271, d130108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20272 q = 1) (hb : d130109 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20272, d130109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20272, d130109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20273 q = 1) (hb : d130110 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20273, d130110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20273, d130110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20274 q = 1) (hb : d130111 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20274, d130111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20274, d130111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro45146 (p : Pattern) (ha : d20306 p = 1) (hb : d130131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h2 (q : Pattern) (ha : d20246 q = 1) (hb : d130083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20247 q = 1) (hb : d130084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h5 (q : Pattern) (ha : d20248 q = 1) (hb : d130085 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20249 q = 1) (hb : d130086 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20250 q = 1) (hb : d130087 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10560 q = 1) (hb : d101790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23377 q ha hb
  have h9 (q : Pattern) (ha : d20302 q = 1) (hb : d130127 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20302, d130127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20302, d130127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20303 q = 1) (hb : d130128 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20303, d130128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20303, d130128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20304 q = 1) (hb : d130129 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20304, d130129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20304, d130129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d20305 q = 1) (hb : d130130 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20305, d130130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20305, d130130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10561 q = 1) (hb : d101791 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10562 q = 1) (hb : d101792 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10563 q = 1) (hb : d101793 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10564 q = 1) (hb : d101794 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d20306 q = 1) (hb : d130131 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20306, d130131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d20306, d130131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro45147 (p : Pattern) (ha : d20312 p = 1) (hb : d130137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20307 q = 1) (hb : d130132 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20307, d130132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45146 q ha hb
    | true =>
      simp only [d20307, d130132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20308 q = 1) (hb : d130133 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20308, d130133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20308, d130133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20309 q = 1) (hb : d130134 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20309, d130134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20309, d130134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20310 q = 1) (hb : d130135 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20310, d130135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20310, d130135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20311 q = 1) (hb : d130136 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20311, d130136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20311, d130136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20312 q = 1) (hb : d130137 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20312, d130137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20312, d130137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45148 (p : Pattern) (ha : d130143 p = 1) (hb : d130326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20275 q = 1) (hb : d130112 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20275, d130112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45144 q ha hb
    | true =>
      simp only [d20275, d130112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45145 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130126 q = 1) (hb : d130322 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130126, d130322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130126, d130322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d20313 q = 1) (hb : d130138 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20313, d130138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45147 q ha hb
    | true =>
      simp only [d20313, d130138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20314 q = 1) (hb : d130139 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20314, d130139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20314, d130139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130140 q = 1) (hb : d130323 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130140, d130323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130140, d130323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d130141 q = 1) (hb : d130324 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130141, d130324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130141, d130324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130142 q = 1) (hb : d130325 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130142, d130325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130142, d130325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130143 q = 1) (hb : d130326 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130143, d130326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130143, d130326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro45149 (p : Pattern) (ha : d130156 p = 1) (hb : d130332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130144 q = 1) (hb : d130327 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130144, d130327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130144, d130327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45148 q ha hb
  have h2 (q : Pattern) (ha : d20330 q = 1) (hb : d130151 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20330, d130151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20330, d130151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45141 q ha hb
  have h3 (q : Pattern) (ha : d130152 q = 1) (hb : d130328 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130152, d130328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130152, d130328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130153 q = 1) (hb : d130329 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130153, d130329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130153, d130329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130154 q = 1) (hb : d130330 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130154, d130330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130154, d130330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130155 q = 1) (hb : d130331 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130155, d130331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130155, d130331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130156 q = 1) (hb : d130332 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130156, d130332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130156, d130332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45150 (p : Pattern) (ha : d130162 p = 1) (hb : d130338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130157 q = 1) (hb : d130333 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130157, d130333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130157, d130333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45149 q ha hb
  have h2 (q : Pattern) (ha : d130158 q = 1) (hb : d130334 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130158, d130334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130158, d130334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130159 q = 1) (hb : d130335 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130159, d130335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130159, d130335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130160 q = 1) (hb : d130336 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130160, d130336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130160, d130336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130161 q = 1) (hb : d130337 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130161, d130337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130161, d130337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130162 q = 1) (hb : d130338 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130162, d130338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130162, d130338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45151 (p : Pattern) (ha : d130168 p = 1) (hb : d130344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d129831 q = 1) (hb : d130261 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129831, d130261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45092 q ha hb
    | true =>
      simp only [d129831, d130261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45103 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129899 q = 1) (hb : d130279 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129899, d130279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129899, d130279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45114 q ha hb
  have h3 (q : Pattern) (ha : d129900 q = 1) (hb : d130280 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129900, d130280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129900, d130280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129986 q = 1) (hb : d130298 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129986, d130298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129986, d130298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45126 q ha hb
  have h5 (q : Pattern) (ha : d129987 q = 1) (hb : d130299 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129987, d130299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129987, d130299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129988 q = 1) (hb : d130300 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129988, d130300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129988, d130300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130074 q = 1) (hb : d130318 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130074, d130318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130074, d130318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45138 q ha hb
  have h8 (q : Pattern) (ha : d130075 q = 1) (hb : d130319 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130075, d130319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130075, d130319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130076 q = 1) (hb : d130320 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130076, d130320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130076, d130320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130077 q = 1) (hb : d130321 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130077, d130321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130077, d130321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130163 q = 1) (hb : d130339 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130163, d130339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130163, d130339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45150 q ha hb
  have h12 (q : Pattern) (ha : d130164 q = 1) (hb : d130340 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130164, d130340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130164, d130340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130165 q = 1) (hb : d130341 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130165, d130341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130165, d130341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130166 q = 1) (hb : d130342 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130166, d130342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130166, d130342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130167 q = 1) (hb : d130343 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130167, d130343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130167, d130343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130168 q = 1) (hb : d130344 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130168, d130344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130168, d130344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro45152 (p : Pattern) (ha : d130174 p = 1) (hb : d130350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130169 q = 1) (hb : d130345 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130169, d130345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45151 q ha hb
    | true =>
      simp only [d130169, d130345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130170 q = 1) (hb : d130346 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130170, d130346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130170, d130346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130171 q = 1) (hb : d130347 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130171, d130347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130171, d130347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130172 q = 1) (hb : d130348 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130172, d130348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130172, d130348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130173 q = 1) (hb : d130349 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130173, d130349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130173, d130349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130174 q = 1) (hb : d130350 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130174, d130350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130174, d130350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45153 (p : Pattern) (ha : d130180 p = 1) (hb : d130356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130175 q = 1) (hb : d130351 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130175, d130351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45152 q ha hb
    | true =>
      simp only [d130175, d130351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130176 q = 1) (hb : d130352 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130176, d130352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130176, d130352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130177 q = 1) (hb : d130353 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130177, d130353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130177, d130353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130178 q = 1) (hb : d130354 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130178, d130354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130178, d130354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130179 q = 1) (hb : d130355 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130179, d130355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130179, d130355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130180 q = 1) (hb : d130356 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130180, d130356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130180, d130356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45154 (p : Pattern) (ha : d130186 p = 1) (hb : d130362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130181 q = 1) (hb : d130357 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130181, d130357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45153 q ha hb
    | true =>
      simp only [d130181, d130357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130182 q = 1) (hb : d130358 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130182, d130358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130182, d130358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130183 q = 1) (hb : d130359 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130183, d130359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130183, d130359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130184 q = 1) (hb : d130360 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130184, d130360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130184, d130360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130185 q = 1) (hb : d130361 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130185, d130361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130185, d130361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130186 q = 1) (hb : d130362 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130186, d130362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130186, d130362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45155 (p : Pattern) (ha : d130192 p = 1) (hb : d130368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130187 q = 1) (hb : d130363 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d130187, d130363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45154 q ha hb
    | true =>
      simp only [d130187, d130363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130188 q = 1) (hb : d130364 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130188, d130364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130188, d130364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130189 q = 1) (hb : d130365 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d130189, d130365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130189, d130365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130190 q = 1) (hb : d130366 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d130190, d130366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130190, d130366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130191 q = 1) (hb : d130367 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d130191, d130367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130191, d130367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130192 q = 1) (hb : d130368 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d130192, d130368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130192, d130368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45156 (p : Pattern) (ha : d130198 p = 1) (hb : d130374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130193 q = 1) (hb : d130369 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d130193, d130369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45155 q ha hb
    | true =>
      simp only [d130193, d130369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130194 q = 1) (hb : d130370 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d130194, d130370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130194, d130370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130195 q = 1) (hb : d130371 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d130195, d130371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130195, d130371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130196 q = 1) (hb : d130372 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d130196, d130372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130196, d130372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130197 q = 1) (hb : d130373 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d130197, d130373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130197, d130373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130198 q = 1) (hb : d130374 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d130198, d130374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130198, d130374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45157 (p : Pattern) (ha : d130204 p = 1) (hb : d130380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130199 q = 1) (hb : d130375 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d130199, d130375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45156 q ha hb
    | true =>
      simp only [d130199, d130375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130200 q = 1) (hb : d130376 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d130200, d130376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130200, d130376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130201 q = 1) (hb : d130377 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d130201, d130377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130201, d130377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130202 q = 1) (hb : d130378 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d130202, d130378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130202, d130378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130203 q = 1) (hb : d130379 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d130203, d130379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130203, d130379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130204 q = 1) (hb : d130380 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d130204, d130380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130204, d130380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45158 (p : Pattern) (ha : d130210 p = 1) (hb : d130386 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130205 q = 1) (hb : d130381 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d130205, d130381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45157 q ha hb
    | true =>
      simp only [d130205, d130381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130206 q = 1) (hb : d130382 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d130206, d130382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130206, d130382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130207 q = 1) (hb : d130383 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d130207, d130383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130207, d130383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130208 q = 1) (hb : d130384 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d130208, d130384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130208, d130384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130209 q = 1) (hb : d130385 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d130209, d130385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130209, d130385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130210 q = 1) (hb : d130386 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d130210, d130386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130210, d130386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45159 (p : Pattern) (ha : d102052 p = 1) (hb : d192722 p = 1) : d188529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20478 q = 1) (hb : d102052 q = 1) : d19846 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, d19846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20478, d19846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44976 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192718 q = 1) : d188525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192718, d188525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192718, d188525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192719 q = 1) : d188526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192719, d188526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192719, d188526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192720 q = 1) : d188527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192720, d188527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192720, d188527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192721 q = 1) : d188528 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192721, d188528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192721, d188528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192722 q = 1) : d188529 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192722, d188529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192722, d188529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45160 (p : Pattern) (ha : d102052 p = 1) (hb : d192732 p = 1) : d188539 p = 1 := by
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
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192728 q = 1) : d188535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192728, d188535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192728, d188535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192729 q = 1) : d188536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192729, d188536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192729, d188536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192730 q = 1) : d188537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192730, d188537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192730, d188537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192731 q = 1) : d188538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192731, d188538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192731, d188538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192732 q = 1) : d188539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192732, d188539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192732, d188539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45161 (p : Pattern) (ha : d102052 p = 1) (hb : d192738 p = 1) : d188545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192733 q = 1) : d188540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192733, d188540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192733, d188540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45160 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192734 q = 1) : d188541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192734, d188541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192734, d188541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192735 q = 1) : d188542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192735, d188542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192735, d188542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192736 q = 1) : d188543 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192736, d188543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192736, d188543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192737 q = 1) : d188544 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192737, d188544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192737, d188544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192738 q = 1) : d188545 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192738, d188545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192738, d188545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45162 (p : Pattern) (ha : d102052 p = 1) (hb : d192744 p = 1) : d188551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192723 q = 1) : d188530 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192723, d188530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192723, d188530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45159 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192724 q = 1) : d188531 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192724, d188531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192724, d188531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192725 q = 1) : d188532 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192725, d188532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192725, d188532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192726 q = 1) : d188533 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192726, d188533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192726, d188533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192727 q = 1) : d188534 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192727, d188534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192727, d188534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192739 q = 1) : d188546 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192739, d188546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192739, d188546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45161 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d192740 q = 1) : d188547 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192740, d188547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192740, d188547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d192741 q = 1) : d188548 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192741, d188548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192741, d188548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d102052 q = 1) (hb : d192742 q = 1) : d188549 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192742, d188549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192742, d188549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d102052 q = 1) (hb : d192743 q = 1) : d188550 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192743, d188550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192743, d188550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102052 q = 1) (hb : d192744 q = 1) : d188551 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192744, d188551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192744, d188551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro45163 (p : Pattern) (ha : d102052 p = 1) (hb : d192750 p = 1) : d188557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192745 q = 1) : d188552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192745, d188552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44992 q hb ha
    | true =>
      simp only [d192745, d188552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro44985 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192746 q = 1) : d188553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192746, d188553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192746, d188553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192747 q = 1) : d188554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192747, d188554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192747, d188554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192748 q = 1) : d188555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192748, d188555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192748, d188555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192749 q = 1) : d188556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192749, d188556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192749, d188556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192750 q = 1) : d188557 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192750, d188557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192750, d188557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45164 (p : Pattern) (ha : d102052 p = 1) (hb : d192756 p = 1) : d188563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192751 q = 1) : d188558 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192751, d188558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192751, d188558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45163 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192752 q = 1) : d188559 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192752, d188559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192752, d188559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192753 q = 1) : d188560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192753, d188560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192753, d188560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192754 q = 1) : d188561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192754, d188561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192754, d188561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192755 q = 1) : d188562 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192755, d188562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192755, d188562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192756 q = 1) : d188563 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192756, d188563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192756, d188563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45165 (p : Pattern) (ha : d102052 p = 1) (hb : d192762 p = 1) : d188569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192757 q = 1) : d188564 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192757, d188564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192757, d188564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45164 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192758 q = 1) : d188565 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192758, d188565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192758, d188565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192759 q = 1) : d188566 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192759, d188566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192759, d188566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192760 q = 1) : d188567 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192760, d188567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192760, d188567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192761 q = 1) : d188568 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192761, d188568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192761, d188568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192762 q = 1) : d188569 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192762, d188569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192762, d188569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45166 (p : Pattern) (ha : d102052 p = 1) (hb : d192769 p = 1) : d188576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192764 q = 1) : d188571 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192764, d188571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45008 q hb ha
    | true =>
      simp only [d192764, d188571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45000 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192765 q = 1) : d188572 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192765, d188572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192765, d188572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192766 q = 1) : d188573 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192766, d188573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192766, d188573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192767 q = 1) : d188574 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192767, d188574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192767, d188574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192768 q = 1) : d188575 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192768, d188575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192768, d188575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192769 q = 1) : d188576 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192769, d188576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192769, d188576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45167 (p : Pattern) (ha : d102052 p = 1) (hb : d192775 p = 1) : d188582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192770 q = 1) : d188577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192770, d188577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192770, d188577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45166 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192771 q = 1) : d188578 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192771, d188578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192771, d188578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192772 q = 1) : d188579 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192772, d188579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192772, d188579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192773 q = 1) : d188580 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192773, d188580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192773, d188580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192774 q = 1) : d188581 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192774, d188581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192774, d188581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192775 q = 1) : d188582 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192775, d188582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192775, d188582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45168 (p : Pattern) (ha : d102052 p = 1) (hb : d192781 p = 1) : d188588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192776 q = 1) : d188583 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192776, d188583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192776, d188583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45167 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192777 q = 1) : d188584 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192777, d188584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192777, d188584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192778 q = 1) : d188585 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192778, d188585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192778, d188585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192779 q = 1) : d188586 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192779, d188586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192779, d188586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192780 q = 1) : d188587 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192780, d188587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192780, d188587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192781 q = 1) : d188588 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192781, d188588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192781, d188588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45169 (p : Pattern) (ha : d102052 p = 1) (hb : d192784 p = 1) : d188592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16673 q = 1) (hb : d102052 q = 1) : d9834 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45020 q ha hb
    | true =>
      simp only [d16673, d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
  have h2 (q : Pattern) (ha : d16674 q = 1) (hb : d102052 q = 1) : d20037 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16674, d20037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16675 q = 1) (hb : d102052 q = 1) : d20038 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16675, d20038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16676 q = 1) (hb : d102052 q = 1) : d9851 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
    | true =>
      simp only [d16676, d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45018 q ha hb
  have h5 (q : Pattern) (ha : d16677 q = 1) (hb : d102052 q = 1) : d20039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16677, d20039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16678 q = 1) (hb : d102052 q = 1) : d20040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16678, d20040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16679 q = 1) (hb : d102052 q = 1) : d20041 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16679, d20041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16693 q = 1) (hb : d102052 q = 1) : d9870 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45014 q ha hb
    | true =>
      simp only [d16693, d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45013 q ha hb
  have h9 (q : Pattern) (ha : d16694 q = 1) (hb : d102052 q = 1) : d20055 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d20055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16694, d20055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16695 q = 1) (hb : d102052 q = 1) : d20056 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d20056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16695, d20056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16696 q = 1) (hb : d102052 q = 1) : d20057 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d20057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16696, d20057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d102052 q = 1) (hb : d171139 q = 1) : d188591 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171139, d188591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171139, d188591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d102052 q = 1) (hb : d129539 q = 1) : d129539 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d102052 q = 1) (hb : d192784 q = 1) : d188592 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192784, d188592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d192784, d188592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro45170 (p : Pattern) (ha : d102052 p = 1) (hb : d192790 p = 1) : d188598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192785 q = 1) : d188593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192785, d188593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45169 q ha hb
    | true =>
      simp only [d192785, d188593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192786 q = 1) : d188594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192786, d188594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192786, d188594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20638 q = 1) (hb : d102052 q = 1) : d20060 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d20060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45015 q ha hb
    | true =>
      simp only [d20638, d20060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20639 q = 1) (hb : d102052 q = 1) : d20061 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d20061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20639, d20061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192787 q = 1) : d188595 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192787, d188595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192787, d188595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192788 q = 1) : d188596 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192788, d188596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192788, d188596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d192789 q = 1) : d188597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192789, d188597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192789, d188597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d192790 q = 1) : d188598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192790, d188598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192790, d188598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45171 (p : Pattern) (ha : d102052 p = 1) (hb : d192796 p = 1) : d188604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192791 q = 1) : d188599 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192791, d188599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45170 q ha hb
    | true =>
      simp only [d192791, d188599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45016 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192792 q = 1) : d188600 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192792, d188600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192792, d188600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192793 q = 1) : d188601 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192793, d188601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192793, d188601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192794 q = 1) : d188602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192794, d188602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192794, d188602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192795 q = 1) : d188603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192795, d188603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192795, d188603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192796 q = 1) : d188604 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192796, d188604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192796, d188604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45172 (p : Pattern) (ha : d102052 p = 1) (hb : d192802 p = 1) : d188610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192797 q = 1) : d188605 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192797, d188605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192797, d188605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45171 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192798 q = 1) : d188606 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192798, d188606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192798, d188606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192799 q = 1) : d188607 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192799, d188607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192799, d188607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192800 q = 1) : d188608 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192800, d188608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192800, d188608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192801 q = 1) : d188609 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192801, d188609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192801, d188609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192802 q = 1) : d188610 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192802, d188610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192802, d188610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45173 (p : Pattern) (ha : d102052 p = 1) (hb : d192808 p = 1) : d188616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192803 q = 1) : d188611 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192803, d188611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192803, d188611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45172 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192804 q = 1) : d188612 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192804, d188612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192804, d188612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192805 q = 1) : d188613 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192805, d188613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192805, d188613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192806 q = 1) : d188614 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192806, d188614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192806, d188614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192807 q = 1) : d188615 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192807, d188615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192807, d188615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192808 q = 1) : d188616 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192808, d188616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192808, d188616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45174 (p : Pattern) (ha : d102052 p = 1) (hb : d192812 p = 1) : d188621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17033 q = 1) (hb : d102052 q = 1) : d10122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45039 q ha hb
    | true =>
      simp only [d17033, d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
  have h2 (q : Pattern) (ha : d17034 q = 1) (hb : d102052 q = 1) : d20141 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17034, d20141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17035 q = 1) (hb : d102052 q = 1) : d20142 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17035, d20142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17036 q = 1) (hb : d102052 q = 1) : d10142 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
    | true =>
      simp only [d17036, d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45037 q ha hb
  have h5 (q : Pattern) (ha : d17037 q = 1) (hb : d102052 q = 1) : d20143 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17037, d20143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17038 q = 1) (hb : d102052 q = 1) : d20144 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17038, d20144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17039 q = 1) (hb : d102052 q = 1) : d20145 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17039, d20145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17053 q = 1) (hb : d102052 q = 1) : d10164 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45033 q ha hb
    | true =>
      simp only [d17053, d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45032 q ha hb
  have h9 (q : Pattern) (ha : d17054 q = 1) (hb : d102052 q = 1) : d20159 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d20159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17054, d20159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17055 q = 1) (hb : d102052 q = 1) : d20160 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d20160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17055, d20160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17056 q = 1) (hb : d102052 q = 1) : d20161 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d20161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17056, d20161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d102052 q = 1) (hb : d171176 q = 1) : d188620 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171176, d188620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171176, d188620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d102052 q = 1) (hb : d129568 q = 1) : d129568 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d102052 q = 1) (hb : d192812 q = 1) : d188621 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192812, d188621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d192812, d188621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro45175 (p : Pattern) (ha : d102052 p = 1) (hb : d192818 p = 1) : d188627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192813 q = 1) : d188622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192813, d188622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45174 q ha hb
    | true =>
      simp only [d192813, d188622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192814 q = 1) : d188623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192814, d188623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192814, d188623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20711 q = 1) (hb : d102052 q = 1) : d20164 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d20164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45034 q ha hb
    | true =>
      simp only [d20711, d20164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20712 q = 1) (hb : d102052 q = 1) : d20165 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d20165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20712, d20165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192815 q = 1) : d188624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192815, d188624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192815, d188624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192816 q = 1) : d188625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192816, d188625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192816, d188625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d192817 q = 1) : d188626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192817, d188626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192817, d188626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d192818 q = 1) : d188627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192818, d188627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192818, d188627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45176 (p : Pattern) (ha : d102052 p = 1) (hb : d192824 p = 1) : d188633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192819 q = 1) : d188628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192819, d188628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45175 q ha hb
    | true =>
      simp only [d192819, d188628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45035 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192820 q = 1) : d188629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192820, d188629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192820, d188629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192821 q = 1) : d188630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192821, d188630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192821, d188630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192822 q = 1) : d188631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192822, d188631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192822, d188631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192823 q = 1) : d188632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192823, d188632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192823, d188632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192824 q = 1) : d188633 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192824, d188633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192824, d188633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45177 (p : Pattern) (ha : d102052 p = 1) (hb : d192830 p = 1) : d188639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192825 q = 1) : d188634 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192825, d188634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192825, d188634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45176 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192826 q = 1) : d188635 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192826, d188635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192826, d188635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192827 q = 1) : d188636 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192827, d188636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192827, d188636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192828 q = 1) : d188637 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192828, d188637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192828, d188637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192829 q = 1) : d188638 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192829, d188638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192829, d188638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192830 q = 1) : d188639 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192830, d188639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192830, d188639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45178 (p : Pattern) (ha : d102052 p = 1) (hb : d192836 p = 1) : d188645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192831 q = 1) : d188640 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192831, d188640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192831, d188640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45177 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192832 q = 1) : d188641 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192832, d188641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192832, d188641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192833 q = 1) : d188642 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192833, d188642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192833, d188642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192834 q = 1) : d188643 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192834, d188643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192834, d188643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192835 q = 1) : d188644 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192835, d188644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192835, d188644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192836 q = 1) : d188645 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192836, d188645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192836, d188645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45179 (p : Pattern) (ha : d102052 p = 1) (hb : d192841 p = 1) : d188651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17397 q = 1) (hb : d102052 q = 1) : d10398 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45058 q ha hb
    | true =>
      simp only [d17397, d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
  have h2 (q : Pattern) (ha : d17398 q = 1) (hb : d102052 q = 1) : d20246 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17398, d20246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17399 q = 1) (hb : d102052 q = 1) : d20247 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17399, d20247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17400 q = 1) (hb : d102052 q = 1) : d10419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
    | true =>
      simp only [d17400, d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45056 q ha hb
  have h5 (q : Pattern) (ha : d17401 q = 1) (hb : d102052 q = 1) : d20248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17401, d20248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17402 q = 1) (hb : d102052 q = 1) : d20249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17402, d20249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17403 q = 1) (hb : d102052 q = 1) : d20250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17403, d20250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17417 q = 1) (hb : d102052 q = 1) : d10441 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45052 q ha hb
    | true =>
      simp only [d17417, d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45051 q ha hb
  have h9 (q : Pattern) (ha : d17418 q = 1) (hb : d102052 q = 1) : d20264 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d20264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17418, d20264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17419 q = 1) (hb : d102052 q = 1) : d20265 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d20265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17419, d20265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17420 q = 1) (hb : d102052 q = 1) : d20266 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d20266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17420, d20266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d102052 q = 1) (hb : d171214 q = 1) : d188650 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d171214, d188650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d171214, d188650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d102052 q = 1) (hb : d129598 q = 1) : d129598 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d102052 q = 1) (hb : d192841 q = 1) : d188651 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d192841, d188651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d192841, d188651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro45180 (p : Pattern) (ha : d102052 p = 1) (hb : d192847 p = 1) : d188657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192842 q = 1) : d188652 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d192842, d188652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45179 q ha hb
    | true =>
      simp only [d192842, d188652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192843 q = 1) : d188653 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d192843, d188653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192843, d188653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20785 q = 1) (hb : d102052 q = 1) : d20269 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d20269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45053 q ha hb
    | true =>
      simp only [d20785, d20269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20786 q = 1) (hb : d102052 q = 1) : d20270 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d20270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20786, d20270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192844 q = 1) : d188654 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d192844, d188654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192844, d188654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192845 q = 1) : d188655 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d192845, d188655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192845, d188655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d192846 q = 1) : d188656 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d192846, d188656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192846, d188656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d192847 q = 1) : d188657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d192847, d188657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192847, d188657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45181 (p : Pattern) (ha : d102052 p = 1) (hb : d192853 p = 1) : d188663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192848 q = 1) : d188658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d192848, d188658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45180 q ha hb
    | true =>
      simp only [d192848, d188658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45054 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192849 q = 1) : d188659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d192849, d188659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192849, d188659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192850 q = 1) : d188660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d192850, d188660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192850, d188660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192851 q = 1) : d188661 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d192851, d188661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192851, d188661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192852 q = 1) : d188662 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192852, d188662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192852, d188662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192853 q = 1) : d188663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d192853, d188663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192853, d188663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45182 (p : Pattern) (ha : d102052 p = 1) (hb : d192859 p = 1) : d188669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192854 q = 1) : d188664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d192854, d188664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192854, d188664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45181 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192855 q = 1) : d188665 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d192855, d188665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192855, d188665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192856 q = 1) : d188666 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d192856, d188666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192856, d188666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192857 q = 1) : d188667 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d192857, d188667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192857, d188667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192858 q = 1) : d188668 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d192858, d188668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192858, d188668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192859 q = 1) : d188669 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d192859, d188669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192859, d188669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45183 (p : Pattern) (ha : d102052 p = 1) (hb : d192865 p = 1) : d188675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192860 q = 1) : d188670 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d192860, d188670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192860, d188670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45182 q ha hb
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192861 q = 1) : d188671 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d192861, d188671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192861, d188671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192862 q = 1) : d188672 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d192862, d188672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192862, d188672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192863 q = 1) : d188673 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d192863, d188673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192863, d188673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192864 q = 1) : d188674 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d192864, d188674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192864, d188674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192865 q = 1) : d188675 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d192865, d188675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d192865, d188675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45184 (p : Pattern) (ha : d102052 p = 1) (hb : d192871 p = 1) : d188681 p = 1 := by
  have h0 (q : Pattern) (ha : d102052 q = 1) (hb : d192763 q = 1) : d188570 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192763, d188570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45162 q ha hb
    | true =>
      simp only [d192763, d188570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45165 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192782 q = 1) : d188589 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192782, d188589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192782, d188589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45168 q ha hb
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192783 q = 1) : d188590 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192783, d188590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d192783, d188590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192809 q = 1) : d188617 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192809, d188617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192809, d188617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45173 q ha hb
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192810 q = 1) : d188618 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192810, d188618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192810, d188618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192811 q = 1) : d188619 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192811, d188619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192811, d188619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102052 q = 1) (hb : d192837 q = 1) : d188646 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192837, d188646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192837, d188646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45178 q ha hb
  have h8 (q : Pattern) (ha : d102052 q = 1) (hb : d192838 q = 1) : d188647 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192838, d188647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192838, d188647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d102052 q = 1) (hb : d192839 q = 1) : d188648 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192839, d188648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192839, d188648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d102052 q = 1) (hb : d192840 q = 1) : d188649 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192840, d188649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192840, d188649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102052 q = 1) (hb : d192866 q = 1) : d188676 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d192866, d188676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192866, d188676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45183 q ha hb
  have h12 (q : Pattern) (ha : d102052 q = 1) (hb : d192867 q = 1) : d188677 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d192867, d188677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192867, d188677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102052 q = 1) (hb : d192868 q = 1) : d188678 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d192868, d188678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192868, d188678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102052 q = 1) (hb : d192869 q = 1) : d188679 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d192869, d188679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d192869, d188679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102052 q = 1) (hb : d192870 q = 1) : d188680 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d192870, d188680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d192870, d188680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d102052 q = 1) (hb : d192871 q = 1) : d188681 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d192871, d188681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d192871, d188681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro45185 (p : Pattern) (ha : d102052 p = 1) (hb : d192877 p = 1) : d188687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192872 q = 1) : d188682 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d192872, d188682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45184 q ha hb
    | true =>
      simp only [d192872, d188682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192873 q = 1) : d188683 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d192873, d188683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192873, d188683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192874 q = 1) : d188684 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d192874, d188684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192874, d188684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192875 q = 1) : d188685 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d192875, d188685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192875, d188685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192876 q = 1) : d188686 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d192876, d188686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192876, d188686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192877 q = 1) : d188687 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d192877, d188687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192877, d188687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45186 (p : Pattern) (ha : d102052 p = 1) (hb : d192883 p = 1) : d188693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192878 q = 1) : d188688 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d192878, d188688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45185 q ha hb
    | true =>
      simp only [d192878, d188688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192879 q = 1) : d188689 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d192879, d188689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192879, d188689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192880 q = 1) : d188690 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d192880, d188690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192880, d188690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192881 q = 1) : d188691 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d192881, d188691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192881, d188691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192882 q = 1) : d188692 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d192882, d188692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192882, d188692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192883 q = 1) : d188693 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d192883, d188693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192883, d188693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45187 (p : Pattern) (ha : d102052 p = 1) (hb : d192889 p = 1) : d188699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192884 q = 1) : d188694 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d192884, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45186 q ha hb
    | true =>
      simp only [d192884, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102052 q = 1) (hb : d192885 q = 1) : d188695 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d192885, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192885, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102052 q = 1) (hb : d192886 q = 1) : d188696 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d192886, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192886, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102052 q = 1) (hb : d192887 q = 1) : d188697 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d192887, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192887, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102052 q = 1) (hb : d192888 q = 1) : d188698 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d192888, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192888, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102052 q = 1) (hb : d192889 q = 1) : d188699 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d192889, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192889, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45188 (p : Pattern) (ha : d190594 p = 1) (hb : d192895 p = 1) : d188705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102052 q = 1) (hb : d192890 q = 1) : d188700 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d192890, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45187 q ha hb
    | true =>
      simp only [d192890, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d190594 q = 1) (hb : d192891 q = 1) : d188701 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d190594, d192891, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d190594, d192891, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d190594 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d190594 q = 1) (hb : d192892 q = 1) : d188702 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d192892, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192892, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d190594 q = 1) (hb : d192893 q = 1) : d188703 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d192893, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192893, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d190594 q = 1) (hb : d192894 q = 1) : d188704 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d192894, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d192894, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d190594 q = 1) (hb : d192895 q = 1) : d188705 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d192895, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d192895, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro45189 (p : Pattern) (ha : d190594 p = 1) (hb : d192901 p = 1) : d188711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190594 q = 1) (hb : d192896 q = 1) : d188706 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d192896, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45188 q ha hb
    | true =>
      simp only [d192896, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d190594 q = 1) (hb : d192897 q = 1) : d188707 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d192897, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192897, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d190594 q = 1) (hb : d192898 q = 1) : d188708 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d192898, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192898, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d190594 q = 1) (hb : d192899 q = 1) : d188709 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d192899, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192899, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d190594 q = 1) (hb : d192900 q = 1) : d188710 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d192900, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192900, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d190594 q = 1) (hb : d192901 q = 1) : d188711 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d192901, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192901, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45190 (p : Pattern) (ha : d190594 p = 1) (hb : d192907 p = 1) : d188717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190594 q = 1) (hb : d192902 q = 1) : d188712 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d192902, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45189 q ha hb
    | true =>
      simp only [d192902, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d190594 q = 1) (hb : d192903 q = 1) : d188713 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d192903, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192903, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d190594 q = 1) (hb : d192904 q = 1) : d188714 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d192904, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192904, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d190594 q = 1) (hb : d192905 q = 1) : d188715 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d192905, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192905, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d190594 q = 1) (hb : d192906 q = 1) : d188716 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d192906, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192906, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d190594 q = 1) (hb : d192907 q = 1) : d188717 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d192907, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192907, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45191 (p : Pattern) (ha : d190594 p = 1) (hb : d192913 p = 1) : d188723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d190594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d190594 q = 1) (hb : d192908 q = 1) : d188718 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d192908, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45190 q ha hb
    | true =>
      simp only [d192908, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d190594 q = 1) (hb : d192909 q = 1) : d188719 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d192909, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d192909, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d190594 q = 1) (hb : d192910 q = 1) : d188720 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d192910, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d192910, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d190594 q = 1) (hb : d192911 q = 1) : d188721 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d192911, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d192911, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d190594 q = 1) (hb : d192912 q = 1) : d188722 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d192912, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d192912, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d190594 q = 1) (hb : d192913 q = 1) : d188723 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d192913, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d192913, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45192 (p : Pattern) (ha : d19845 p = 1) (hb : d129716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129711 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19749 q = 1) (hb : d129684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19749, d129684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45079 q ha hb
    | true =>
      simp only [d19749, d129684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19841 q = 1) (hb : d129712 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19841, d129712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19841, d129712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129685 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d19842 q = 1) (hb : d129713 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19842, d129713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19842, d129713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19843 q = 1) (hb : d129714 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19843, d129714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19843, d129714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19844 q = 1) (hb : d129715 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19844, d129715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19844, d129715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19845 q = 1) (hb : d129716 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19845, d129716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19845, d129716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45193 (p : Pattern) (ha : d129722 p = 1) (hb : d188529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19846 q = 1) (hb : d129717 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d129717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d129717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45192 q ha hb
  have h2 (q : Pattern) (ha : d129718 q = 1) (hb : d188525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129718, d188525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129718, d188525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129719 q = 1) (hb : d188526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129719, d188526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129719, d188526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129720 q = 1) (hb : d188527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129720, d188527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129720, d188527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129721 q = 1) (hb : d188528 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129721, d188528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129721, d188528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129722 q = 1) (hb : d188529 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129722, d188529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129722, d188529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45194 (p : Pattern) (ha : d129750 p = 1) (hb : d188539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d19776 q = 1) (hb : d129711 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19776, d129711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45083 q ha hb
    | true =>
      simp only [d19776, d129711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45079 q ha hb
  have h3 (q : Pattern) (ha : d129740 q = 1) (hb : d188535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129740, d188535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129740, d188535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129746 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129747 q = 1) (hb : d188536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129747, d188536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129747, d188536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129748 q = 1) (hb : d188537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129748, d188537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129748, d188537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129749 q = 1) (hb : d188538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129749, d188538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129749, d188538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129750 q = 1) (hb : d188539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129750, d188539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129750, d188539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45195 (p : Pattern) (ha : d129762 p = 1) (hb : d188545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129751 q = 1) (hb : d188540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129751, d188540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129751, d188540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45194 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129757 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129758 q = 1) (hb : d188541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129758, d188541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129758, d188541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129759 q = 1) (hb : d188542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129759, d188542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129759, d188542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129760 q = 1) (hb : d188543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129760, d188543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129760, d188543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129761 q = 1) (hb : d188544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129761, d188544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129761, d188544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129762 q = 1) (hb : d188545 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129762, d188545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129762, d188545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45196 (p : Pattern) (ha : d129768 p = 1) (hb : d188551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129699 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129723 q = 1) (hb : d188530 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129723, d188530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129723, d188530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45193 q ha hb
  have h3 (q : Pattern) (ha : d129724 q = 1) (hb : d188531 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129724, d188531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129724, d188531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129725 q = 1) (hb : d188532 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129725, d188532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129725, d188532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129726 q = 1) (hb : d188533 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129726, d188533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129726, d188533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129727 q = 1) (hb : d188534 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129727, d188534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129727, d188534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129763 q = 1) (hb : d188546 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129763, d188546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129763, d188546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45195 q ha hb
  have h8 (q : Pattern) (ha : d129764 q = 1) (hb : d188547 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129764, d188547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129764, d188547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129765 q = 1) (hb : d188548 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129765, d188548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129765, d188548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129766 q = 1) (hb : d188549 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129766, d188549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129766, d188549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129767 q = 1) (hb : d188550 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129767, d188550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129767, d188550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129768 q = 1) (hb : d188551 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129768, d188551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129768, d188551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45197 (p : Pattern) (ha : d129811 p = 1) (hb : d188557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129800 q = 1) (hb : d188552 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129800, d188552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45099 q hb ha
    | true =>
      simp only [d129800, d188552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45094 q hb ha
  have h3 (q : Pattern) (ha : d129801 q = 1) (hb : d188553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129801, d188553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129801, d188553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129807 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129808 q = 1) (hb : d188554 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129808, d188554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129808, d188554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129809 q = 1) (hb : d188555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129809, d188555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129809, d188555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129810 q = 1) (hb : d188556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129810, d188556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129810, d188556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129811 q = 1) (hb : d188557 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129811, d188557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129811, d188557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45198 (p : Pattern) (ha : d129824 p = 1) (hb : d188563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129812 q = 1) (hb : d188558 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129812, d188558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129812, d188558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45197 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129819 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129820 q = 1) (hb : d188559 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129820, d188559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129820, d188559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129821 q = 1) (hb : d188560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129821, d188560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129821, d188560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129822 q = 1) (hb : d188561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129822, d188561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129822, d188561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129823 q = 1) (hb : d188562 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129823, d188562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129823, d188562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129824 q = 1) (hb : d188563 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129824, d188563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129824, d188563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45199 (p : Pattern) (ha : d129830 p = 1) (hb : d188569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129825 q = 1) (hb : d188564 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129825, d188564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129825, d188564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45198 q ha hb
  have h2 (q : Pattern) (ha : d129826 q = 1) (hb : d188565 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129826, d188565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129826, d188565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129827 q = 1) (hb : d188566 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129827, d188566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129827, d188566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129828 q = 1) (hb : d188567 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129828, d188567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129828, d188567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129829 q = 1) (hb : d188568 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129829, d188568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129829, d188568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129830 q = 1) (hb : d188569 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129830, d188569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129830, d188569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45200 (p : Pattern) (ha : d129879 p = 1) (hb : d188576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129863 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129868 q = 1) (hb : d188571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129868, d188571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45110 q hb ha
    | true =>
      simp only [d129868, d188571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45105 q hb ha
  have h3 (q : Pattern) (ha : d129869 q = 1) (hb : d188572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129869, d188572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129869, d188572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129875 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129876 q = 1) (hb : d188573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129876, d188573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129876, d188573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129877 q = 1) (hb : d188574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129877, d188574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129877, d188574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129878 q = 1) (hb : d188575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129878, d188575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129878, d188575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129879 q = 1) (hb : d188576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129879, d188576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129879, d188576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45201 (p : Pattern) (ha : d129892 p = 1) (hb : d188582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129880 q = 1) (hb : d188577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129880, d188577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129880, d188577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45200 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129887 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129888 q = 1) (hb : d188578 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129888, d188578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129888, d188578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129889 q = 1) (hb : d188579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129889, d188579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129889, d188579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129890 q = 1) (hb : d188580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129890, d188580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129890, d188580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129891 q = 1) (hb : d188581 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129891, d188581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129891, d188581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129892 q = 1) (hb : d188582 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129892, d188582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129892, d188582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45202 (p : Pattern) (ha : d129898 p = 1) (hb : d188588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129893 q = 1) (hb : d188583 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129893, d188583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129893, d188583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45201 q ha hb
  have h2 (q : Pattern) (ha : d129894 q = 1) (hb : d188584 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129894, d188584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129894, d188584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129895 q = 1) (hb : d188585 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129895, d188585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129895, d188585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129896 q = 1) (hb : d188586 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129896, d188586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129896, d188586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129897 q = 1) (hb : d188587 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129897, d188587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129897, d188587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129898 q = 1) (hb : d188588 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129898, d188588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129898, d188588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45203 (p : Pattern) (ha : d129937 p = 1) (hb : d188592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h2 (q : Pattern) (ha : d20037 q = 1) (hb : d129906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20037, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20037, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20038 q = 1) (hb : d129907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20038, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20038, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h5 (q : Pattern) (ha : d20039 q = 1) (hb : d129908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20039, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20039, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20040 q = 1) (hb : d129909 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20040, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20040, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20041 q = 1) (hb : d129910 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20041, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20041, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h9 (q : Pattern) (ha : d20055 q = 1) (hb : d129924 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20055, d129924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20055, d129924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20056 q = 1) (hb : d129925 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20056, d129925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20056, d129925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20057 q = 1) (hb : d129926 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20057, d129926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20057, d129926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d129936 q = 1) (hb : d188591 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129936, d188591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d129936, d188591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9871 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9872 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9873 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d101404 q = 1) (hb : d129539 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101404, d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d101404, d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d129937 q = 1) (hb : d188592 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129937, d188592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d129937, d188592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro45204 (p : Pattern) (ha : d129943 p = 1) (hb : d188598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129938 q = 1) (hb : d188593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129938, d188593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45203 q ha hb
    | true =>
      simp only [d129938, d188593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129939 q = 1) (hb : d188594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129939, d188594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129939, d188594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20060 q = 1) (hb : d129929 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20060, d129929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45115 q ha hb
    | true =>
      simp only [d20060, d129929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20061 q = 1) (hb : d129930 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20061, d129930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20061, d129930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129940 q = 1) (hb : d188595 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129940, d188595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129940, d188595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129941 q = 1) (hb : d188596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129941, d188596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129941, d188596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129942 q = 1) (hb : d188597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129942, d188597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129942, d188597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129943 q = 1) (hb : d188598 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129943, d188598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129943, d188598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45205 (p : Pattern) (ha : d129966 p = 1) (hb : d188604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129948 q = 1) (hb : d188599 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129948, d188599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45204 q ha hb
    | true =>
      simp only [d129948, d188599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45116 q hb ha
  have h3 (q : Pattern) (ha : d129949 q = 1) (hb : d188600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129949, d188600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129949, d188600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d129962 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129963 q = 1) (hb : d188601 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129963, d188601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129963, d188601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129964 q = 1) (hb : d188602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129964, d188602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129964, d188602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129965 q = 1) (hb : d188603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129965, d188603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129965, d188603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129966 q = 1) (hb : d188604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129966, d188604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129966, d188604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45206 (p : Pattern) (ha : d129979 p = 1) (hb : d188610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129967 q = 1) (hb : d188605 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129967, d188605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129967, d188605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45205 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129974 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129975 q = 1) (hb : d188606 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129975, d188606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129975, d188606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129976 q = 1) (hb : d188607 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129976, d188607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129976, d188607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129977 q = 1) (hb : d188608 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129977, d188608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129977, d188608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129978 q = 1) (hb : d188609 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129978, d188609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129978, d188609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129979 q = 1) (hb : d188610 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129979, d188610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129979, d188610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45207 (p : Pattern) (ha : d129985 p = 1) (hb : d188616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129980 q = 1) (hb : d188611 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129980, d188611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129980, d188611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45206 q ha hb
  have h2 (q : Pattern) (ha : d129981 q = 1) (hb : d188612 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129981, d188612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129981, d188612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129982 q = 1) (hb : d188613 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129982, d188613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129982, d188613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129983 q = 1) (hb : d188614 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129983, d188614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129983, d188614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129984 q = 1) (hb : d188615 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129984, d188615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129984, d188615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129985 q = 1) (hb : d188616 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129985, d188616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129985, d188616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45208 (p : Pattern) (ha : d130025 p = 1) (hb : d188621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h2 (q : Pattern) (ha : d20141 q = 1) (hb : d129994 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20142 q = 1) (hb : d129995 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h5 (q : Pattern) (ha : d20143 q = 1) (hb : d129996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20144 q = 1) (hb : d129997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20145 q = 1) (hb : d129998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h9 (q : Pattern) (ha : d20159 q = 1) (hb : d130012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20159, d130012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20159, d130012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20160 q = 1) (hb : d130013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20160, d130013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20160, d130013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20161 q = 1) (hb : d130014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20161, d130014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20161, d130014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d130024 q = 1) (hb : d188620 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d130024, d188620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d130024, d188620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10165 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10166 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10167 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d101604 q = 1) (hb : d129568 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101604, d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d101604, d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d130025 q = 1) (hb : d188621 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130025, d188621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130025, d188621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro45209 (p : Pattern) (ha : d130031 p = 1) (hb : d188627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130026 q = 1) (hb : d188622 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130026, d188622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45208 q ha hb
    | true =>
      simp only [d130026, d188622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130027 q = 1) (hb : d188623 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130027, d188623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130027, d188623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20164 q = 1) (hb : d130017 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d130017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45127 q ha hb
    | true =>
      simp only [d20164, d130017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20165 q = 1) (hb : d130018 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d130018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20165, d130018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130028 q = 1) (hb : d188624 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130028, d188624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130028, d188624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130029 q = 1) (hb : d188625 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130029, d188625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130029, d188625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130030 q = 1) (hb : d188626 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130030, d188626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130030, d188626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130031 q = 1) (hb : d188627 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130031, d188627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130031, d188627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45210 (p : Pattern) (ha : d130054 p = 1) (hb : d188633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130023 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130036 q = 1) (hb : d188628 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130036, d188628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45209 q ha hb
    | true =>
      simp only [d130036, d188628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45128 q hb ha
  have h3 (q : Pattern) (ha : d130037 q = 1) (hb : d188629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130037, d188629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130037, d188629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130050 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130051 q = 1) (hb : d188630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130051, d188630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130051, d188630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130052 q = 1) (hb : d188631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130052, d188631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130052, d188631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130053 q = 1) (hb : d188632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130053, d188632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130053, d188632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130054 q = 1) (hb : d188633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130054, d188633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130054, d188633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45211 (p : Pattern) (ha : d130067 p = 1) (hb : d188639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130055 q = 1) (hb : d188634 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130055, d188634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130055, d188634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45210 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130062 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130063 q = 1) (hb : d188635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130063, d188635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130063, d188635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130064 q = 1) (hb : d188636 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130064, d188636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130064, d188636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130065 q = 1) (hb : d188637 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130065, d188637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130065, d188637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130066 q = 1) (hb : d188638 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130066, d188638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130066, d188638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130067 q = 1) (hb : d188639 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130067, d188639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130067, d188639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45212 (p : Pattern) (ha : d130073 p = 1) (hb : d188645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130068 q = 1) (hb : d188640 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130068, d188640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130068, d188640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45211 q ha hb
  have h2 (q : Pattern) (ha : d130069 q = 1) (hb : d188641 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130069, d188641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130069, d188641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130070 q = 1) (hb : d188642 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130070, d188642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130070, d188642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130071 q = 1) (hb : d188643 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130071, d188643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130071, d188643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130072 q = 1) (hb : d188644 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130072, d188644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130072, d188644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130073 q = 1) (hb : d188645 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130073, d188645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130073, d188645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45213 (p : Pattern) (ha : d130114 p = 1) (hb : d188651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h2 (q : Pattern) (ha : d20246 q = 1) (hb : d130083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20247 q = 1) (hb : d130084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h5 (q : Pattern) (ha : d20248 q = 1) (hb : d130085 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20249 q = 1) (hb : d130086 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20250 q = 1) (hb : d130087 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h9 (q : Pattern) (ha : d20264 q = 1) (hb : d130101 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20264, d130101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20264, d130101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20265 q = 1) (hb : d130102 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20265, d130102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20265, d130102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20266 q = 1) (hb : d130103 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20266, d130103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20266, d130103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d130113 q = 1) (hb : d188650 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d130113, d188650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d130113, d188650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10442 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10443 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10444 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d101775 q = 1) (hb : d129598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101775, d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
    | true =>
      simp only [d101775, d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  have h22 (q : Pattern) (ha : d130114 q = 1) (hb : d188651 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130114, d188651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130114, d188651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro45214 (p : Pattern) (ha : d130120 p = 1) (hb : d188657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130115 q = 1) (hb : d188652 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130115, d188652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45213 q ha hb
    | true =>
      simp only [d130115, d188652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130116 q = 1) (hb : d188653 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130116, d188653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130116, d188653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20269 q = 1) (hb : d130106 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d130106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45139 q ha hb
    | true =>
      simp only [d20269, d130106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20270 q = 1) (hb : d130107 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d130107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20270, d130107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130117 q = 1) (hb : d188654 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130117, d188654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130117, d188654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130118 q = 1) (hb : d188655 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130118, d188655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130118, d188655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130119 q = 1) (hb : d188656 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130119, d188656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130119, d188656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130120 q = 1) (hb : d188657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130120, d188657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130120, d188657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro45215 (p : Pattern) (ha : d130143 p = 1) (hb : d188663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130125 q = 1) (hb : d188658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130125, d188658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45214 q ha hb
    | true =>
      simp only [d130125, d188658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45140 q hb ha
  have h3 (q : Pattern) (ha : d130126 q = 1) (hb : d188659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130126, d188659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130126, d188659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130139 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130140 q = 1) (hb : d188660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130140, d188660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130140, d188660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130141 q = 1) (hb : d188661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130141, d188661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130141, d188661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130142 q = 1) (hb : d188662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130142, d188662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130142, d188662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130143 q = 1) (hb : d188663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130143, d188663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130143, d188663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45216 (p : Pattern) (ha : d130156 p = 1) (hb : d188669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130144 q = 1) (hb : d188664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130144, d188664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130144, d188664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45215 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130151 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130152 q = 1) (hb : d188665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130152, d188665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130152, d188665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130153 q = 1) (hb : d188666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130153, d188666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130153, d188666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130154 q = 1) (hb : d188667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130154, d188667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130154, d188667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130155 q = 1) (hb : d188668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130155, d188668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130155, d188668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130156 q = 1) (hb : d188669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130156, d188669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130156, d188669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45217 (p : Pattern) (ha : d130162 p = 1) (hb : d188675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130157 q = 1) (hb : d188670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130157, d188670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130157, d188670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45216 q ha hb
  have h2 (q : Pattern) (ha : d130158 q = 1) (hb : d188671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130158, d188671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130158, d188671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130159 q = 1) (hb : d188672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130159, d188672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130159, d188672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130160 q = 1) (hb : d188673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130160, d188673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130160, d188673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130161 q = 1) (hb : d188674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130161, d188674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130161, d188674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130162 q = 1) (hb : d188675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130162, d188675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130162, d188675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45218 (p : Pattern) (ha : d130168 p = 1) (hb : d188681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d129831 q = 1) (hb : d188570 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129831, d188570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45196 q ha hb
    | true =>
      simp only [d129831, d188570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45199 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129899 q = 1) (hb : d188589 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129899, d188589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129899, d188589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45202 q ha hb
  have h3 (q : Pattern) (ha : d129900 q = 1) (hb : d188590 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129900, d188590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129900, d188590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129986 q = 1) (hb : d188617 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129986, d188617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129986, d188617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45207 q ha hb
  have h5 (q : Pattern) (ha : d129987 q = 1) (hb : d188618 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129987, d188618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129987, d188618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129988 q = 1) (hb : d188619 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129988, d188619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129988, d188619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130074 q = 1) (hb : d188646 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130074, d188646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130074, d188646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45212 q ha hb
  have h8 (q : Pattern) (ha : d130075 q = 1) (hb : d188647 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130075, d188647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130075, d188647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130076 q = 1) (hb : d188648 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130076, d188648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130076, d188648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130077 q = 1) (hb : d188649 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130077, d188649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130077, d188649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130163 q = 1) (hb : d188676 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130163, d188676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130163, d188676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45217 q ha hb
  have h12 (q : Pattern) (ha : d130164 q = 1) (hb : d188677 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130164, d188677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130164, d188677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130165 q = 1) (hb : d188678 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130165, d188678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130165, d188678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130166 q = 1) (hb : d188679 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130166, d188679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130166, d188679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130167 q = 1) (hb : d188680 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130167, d188680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130167, d188680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130168 q = 1) (hb : d188681 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130168, d188681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130168, d188681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro45219 (p : Pattern) (ha : d130174 p = 1) (hb : d188687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130169 q = 1) (hb : d188682 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130169, d188682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45218 q ha hb
    | true =>
      simp only [d130169, d188682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130170 q = 1) (hb : d188683 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130170, d188683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130170, d188683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130171 q = 1) (hb : d188684 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130171, d188684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130171, d188684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130172 q = 1) (hb : d188685 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130172, d188685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130172, d188685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130173 q = 1) (hb : d188686 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130173, d188686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130173, d188686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130174 q = 1) (hb : d188687 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130174, d188687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130174, d188687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45220 (p : Pattern) (ha : d130180 p = 1) (hb : d188693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130175 q = 1) (hb : d188688 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130175, d188688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45219 q ha hb
    | true =>
      simp only [d130175, d188688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130176 q = 1) (hb : d188689 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130176, d188689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130176, d188689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130177 q = 1) (hb : d188690 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130177, d188690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130177, d188690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130178 q = 1) (hb : d188691 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130178, d188691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130178, d188691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130179 q = 1) (hb : d188692 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130179, d188692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130179, d188692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130180 q = 1) (hb : d188693 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130180, d188693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130180, d188693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45221 (p : Pattern) (ha : d130186 p = 1) (hb : d188699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130181 q = 1) (hb : d188694 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130181, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45220 q ha hb
    | true =>
      simp only [d130181, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130182 q = 1) (hb : d188695 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130182, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130182, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130183 q = 1) (hb : d188696 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130183, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130183, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130184 q = 1) (hb : d188697 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130184, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130184, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130185 q = 1) (hb : d188698 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130185, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130185, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130186 q = 1) (hb : d188699 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130186, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130186, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45222 (p : Pattern) (ha : d130192 p = 1) (hb : d188705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130187 q = 1) (hb : d188700 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d130187, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45221 q ha hb
    | true =>
      simp only [d130187, d188700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130188 q = 1) (hb : d188701 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130188, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130188, d188701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130189 q = 1) (hb : d188702 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d130189, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130189, d188702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130190 q = 1) (hb : d188703 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d130190, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130190, d188703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130191 q = 1) (hb : d188704 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d130191, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130191, d188704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130192 q = 1) (hb : d188705 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d130192, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130192, d188705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45223 (p : Pattern) (ha : d130198 p = 1) (hb : d188711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130193 q = 1) (hb : d188706 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d130193, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45222 q ha hb
    | true =>
      simp only [d130193, d188706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130194 q = 1) (hb : d188707 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d130194, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130194, d188707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130195 q = 1) (hb : d188708 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d130195, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130195, d188708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130196 q = 1) (hb : d188709 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d130196, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130196, d188709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130197 q = 1) (hb : d188710 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d130197, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130197, d188710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130198 q = 1) (hb : d188711 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d130198, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130198, d188711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45224 (p : Pattern) (ha : d130204 p = 1) (hb : d188717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130199 q = 1) (hb : d188712 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d130199, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45223 q ha hb
    | true =>
      simp only [d130199, d188712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130200 q = 1) (hb : d188713 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d130200, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130200, d188713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130201 q = 1) (hb : d188714 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d130201, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130201, d188714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130202 q = 1) (hb : d188715 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d130202, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130202, d188715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130203 q = 1) (hb : d188716 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d130203, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130203, d188716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130204 q = 1) (hb : d188717 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d130204, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130204, d188717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45225 (p : Pattern) (ha : d130210 p = 1) (hb : d188723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130205 q = 1) (hb : d188718 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d130205, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45224 q ha hb
    | true =>
      simp only [d130205, d188718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130206 q = 1) (hb : d188719 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d130206, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130206, d188719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130207 q = 1) (hb : d188720 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d130207, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130207, d188720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130208 q = 1) (hb : d188721 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d130208, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130208, d188721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130209 q = 1) (hb : d188722 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d130209, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130209, d188722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130210 q = 1) (hb : d188723 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d130210, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130210, d188723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro45226 (p : Pattern) (ha : d19845 p = 1) (hb : d130215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d19776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19749 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d19841 q = 1) (hb : d130211 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19841, d130211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19841, d130211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d19750 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d19842 q = 1) (hb : d130212 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19842, d130212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19842, d130212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19843 q = 1) (hb : d130213 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19843, d130213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19843, d130213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19844 q = 1) (hb : d130214 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19844, d130214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19844, d130214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19845 q = 1) (hb : d130215 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19845, d130215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19845, d130215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45227 (p : Pattern) (ha : d130221 p = 1) (hb : d188529 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19846 q = 1) (hb : d130216 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19846, d130216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19846, d130216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45226 q ha hb
  have h2 (q : Pattern) (ha : d130217 q = 1) (hb : d188525 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130217, d188525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130217, d188525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130218 q = 1) (hb : d188526 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130218, d188526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130218, d188526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130219 q = 1) (hb : d188527 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130219, d188527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130219, d188527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130220 q = 1) (hb : d188528 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130220, d188528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130220, d188528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130221 q = 1) (hb : d188529 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130221, d188529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130221, d188529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45228 (p : Pattern) (ha : d130231 p = 1) (hb : d188539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d19816 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130227 q = 1) (hb : d188535 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130227, d188535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130227, d188535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d19835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130228 q = 1) (hb : d188536 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130228, d188536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130228, d188536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130229 q = 1) (hb : d188537 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130229, d188537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130229, d188537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130230 q = 1) (hb : d188538 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130230, d188538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130230, d188538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130231 q = 1) (hb : d188539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130231, d188539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130231, d188539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45229 (p : Pattern) (ha : d130237 p = 1) (hb : d188545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130232 q = 1) (hb : d188540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130232, d188540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130232, d188540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45228 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19846 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130233 q = 1) (hb : d188541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130233, d188541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130233, d188541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130234 q = 1) (hb : d188542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130234, d188542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130234, d188542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130235 q = 1) (hb : d188543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130235, d188543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130235, d188543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130236 q = 1) (hb : d188544 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130236, d188544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130236, d188544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130237 q = 1) (hb : d188545 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130237, d188545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130237, d188545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45230 (p : Pattern) (ha : d130243 p = 1) (hb : d188551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d19764 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130222 q = 1) (hb : d188530 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130222, d188530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130222, d188530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45227 q ha hb
  have h3 (q : Pattern) (ha : d130223 q = 1) (hb : d188531 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130223, d188531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130223, d188531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130224 q = 1) (hb : d188532 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130224, d188532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130224, d188532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130225 q = 1) (hb : d188533 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130225, d188533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130225, d188533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130226 q = 1) (hb : d188534 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130226, d188534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130226, d188534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130238 q = 1) (hb : d188546 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130238, d188546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130238, d188546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45229 q ha hb
  have h8 (q : Pattern) (ha : d130239 q = 1) (hb : d188547 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130239, d188547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130239, d188547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130240 q = 1) (hb : d188548 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130240, d188548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130240, d188548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130241 q = 1) (hb : d188549 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130241, d188549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130241, d188549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130242 q = 1) (hb : d188550 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130242, d188550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130242, d188550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130243 q = 1) (hb : d188551 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130243, d188551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130243, d188551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro45231 (p : Pattern) (ha : d130248 p = 1) (hb : d188557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d19884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188552 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130244 q = 1) (hb : d188553 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130244, d188553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130244, d188553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d19912 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130245 q = 1) (hb : d188554 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130245, d188554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130245, d188554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130246 q = 1) (hb : d188555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130246, d188555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130246, d188555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130247 q = 1) (hb : d188556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130247, d188556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130247, d188556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130248 q = 1) (hb : d188557 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130248, d188557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130248, d188557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45232 (p : Pattern) (ha : d130254 p = 1) (hb : d188563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130249 q = 1) (hb : d188558 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130249, d188558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130249, d188558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45231 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d19928 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130250 q = 1) (hb : d188559 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130250, d188559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130250, d188559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130251 q = 1) (hb : d188560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130251, d188560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130251, d188560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130252 q = 1) (hb : d188561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130252, d188561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130252, d188561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130253 q = 1) (hb : d188562 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130253, d188562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130253, d188562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130254 q = 1) (hb : d188563 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130254, d188563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130254, d188563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45233 (p : Pattern) (ha : d130260 p = 1) (hb : d188569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130255 q = 1) (hb : d188564 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130255, d188564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130255, d188564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45232 q ha hb
  have h2 (q : Pattern) (ha : d130256 q = 1) (hb : d188565 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130256, d188565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130256, d188565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130257 q = 1) (hb : d188566 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130257, d188566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130257, d188566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130258 q = 1) (hb : d188567 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130258, d188567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130258, d188567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130259 q = 1) (hb : d188568 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130259, d188568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130259, d188568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130260 q = 1) (hb : d188569 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130260, d188569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130260, d188569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45234 (p : Pattern) (ha : d130266 p = 1) (hb : d188576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d19972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188571 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130262 q = 1) (hb : d188572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130262, d188572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130262, d188572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20002 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130263 q = 1) (hb : d188573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130263, d188573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130263, d188573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130264 q = 1) (hb : d188574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130264, d188574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130264, d188574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130265 q = 1) (hb : d188575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130265, d188575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130265, d188575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130266 q = 1) (hb : d188576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130266, d188576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130266, d188576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45235 (p : Pattern) (ha : d130272 p = 1) (hb : d188582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130267 q = 1) (hb : d188577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130267, d188577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130267, d188577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45234 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20018 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130268 q = 1) (hb : d188578 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130268, d188578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130268, d188578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130269 q = 1) (hb : d188579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130269, d188579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130269, d188579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130270 q = 1) (hb : d188580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130270, d188580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130270, d188580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130271 q = 1) (hb : d188581 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130271, d188581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130271, d188581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130272 q = 1) (hb : d188582 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130272, d188582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130272, d188582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45236 (p : Pattern) (ha : d130278 p = 1) (hb : d188588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130273 q = 1) (hb : d188583 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130273, d188583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130273, d188583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45235 q ha hb
  have h2 (q : Pattern) (ha : d130274 q = 1) (hb : d188584 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130274, d188584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130274, d188584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130275 q = 1) (hb : d188585 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130275, d188585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130275, d188585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130276 q = 1) (hb : d188586 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130276, d188586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130276, d188586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130277 q = 1) (hb : d188587 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130277, d188587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130277, d188587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130278 q = 1) (hb : d188588 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130278, d188588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130278, d188588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45237 (p : Pattern) (ha : d130285 p = 1) (hb : d188604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188599 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130281 q = 1) (hb : d188600 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130281, d188600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130281, d188600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130282 q = 1) (hb : d188601 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130282, d188601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130282, d188601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130283 q = 1) (hb : d188602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130283, d188602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130283, d188602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130284 q = 1) (hb : d188603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130284, d188603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130284, d188603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130285 q = 1) (hb : d188604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130285, d188604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130285, d188604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45238 (p : Pattern) (ha : d130291 p = 1) (hb : d188610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130286 q = 1) (hb : d188605 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130286, d188605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130286, d188605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45237 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20121 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130287 q = 1) (hb : d188606 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130287, d188606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130287, d188606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130288 q = 1) (hb : d188607 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130288, d188607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130288, d188607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130289 q = 1) (hb : d188608 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130289, d188608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130289, d188608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130290 q = 1) (hb : d188609 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130290, d188609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130290, d188609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130291 q = 1) (hb : d188610 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130291, d188610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130291, d188610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45239 (p : Pattern) (ha : d130297 p = 1) (hb : d188616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130292 q = 1) (hb : d188611 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130292, d188611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130292, d188611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45238 q ha hb
  have h2 (q : Pattern) (ha : d130293 q = 1) (hb : d188612 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130293, d188612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130293, d188612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130294 q = 1) (hb : d188613 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130294, d188613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130294, d188613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130295 q = 1) (hb : d188614 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130295, d188614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130295, d188614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130296 q = 1) (hb : d188615 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130296, d188615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130296, d188615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130297 q = 1) (hb : d188616 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130297, d188616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130297, d188616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45240 (p : Pattern) (ha : d130305 p = 1) (hb : d188633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20170 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188628 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130301 q = 1) (hb : d188629 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130301, d188629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130301, d188629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130302 q = 1) (hb : d188630 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130302, d188630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130302, d188630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130303 q = 1) (hb : d188631 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130303, d188631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130303, d188631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130304 q = 1) (hb : d188632 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130304, d188632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130304, d188632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130305 q = 1) (hb : d188633 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130305, d188633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130305, d188633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45241 (p : Pattern) (ha : d130311 p = 1) (hb : d188639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130306 q = 1) (hb : d188634 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130306, d188634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130306, d188634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45240 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20225 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130307 q = 1) (hb : d188635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130307, d188635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130307, d188635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130308 q = 1) (hb : d188636 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130308, d188636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130308, d188636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130309 q = 1) (hb : d188637 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130309, d188637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130309, d188637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130310 q = 1) (hb : d188638 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130310, d188638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130310, d188638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130311 q = 1) (hb : d188639 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130311, d188639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130311, d188639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45242 (p : Pattern) (ha : d130317 p = 1) (hb : d188645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130312 q = 1) (hb : d188640 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130312, d188640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130312, d188640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45241 q ha hb
  have h2 (q : Pattern) (ha : d130313 q = 1) (hb : d188641 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130313, d188641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130313, d188641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130314 q = 1) (hb : d188642 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130314, d188642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130314, d188642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130315 q = 1) (hb : d188643 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130315, d188643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130315, d188643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130316 q = 1) (hb : d188644 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130316, d188644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130316, d188644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130317 q = 1) (hb : d188645 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130317, d188645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130317, d188645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45243 (p : Pattern) (ha : d130326 p = 1) (hb : d188663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20275 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d188658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130322 q = 1) (hb : d188659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130322, d188659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130322, d188659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20314 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130323 q = 1) (hb : d188660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130323, d188660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130323, d188660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130324 q = 1) (hb : d188661 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130324, d188661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130324, d188661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130325 q = 1) (hb : d188662 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130325, d188662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130325, d188662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130326 q = 1) (hb : d188663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130326, d188663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130326, d188663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro45244 (p : Pattern) (ha : d130332 p = 1) (hb : d188669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130327 q = 1) (hb : d188664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130327, d188664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130327, d188664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45243 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20330 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130328 q = 1) (hb : d188665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130328, d188665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130328, d188665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130329 q = 1) (hb : d188666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130329, d188666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130329, d188666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130330 q = 1) (hb : d188667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130330, d188667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130330, d188667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130331 q = 1) (hb : d188668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130331, d188668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130331, d188668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130332 q = 1) (hb : d188669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130332, d188669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130332, d188669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro45245 (p : Pattern) (ha : d130338 p = 1) (hb : d188675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130333 q = 1) (hb : d188670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130333, d188670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130333, d188670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45244 q ha hb
  have h2 (q : Pattern) (ha : d130334 q = 1) (hb : d188671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130334, d188671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130334, d188671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130335 q = 1) (hb : d188672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130335, d188672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130335, d188672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130336 q = 1) (hb : d188673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130336, d188673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130336, d188673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130337 q = 1) (hb : d188674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130337, d188674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130337, d188674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130338 q = 1) (hb : d188675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130338, d188675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130338, d188675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro45246 (p : Pattern) (ha : d130344 p = 1) (hb : d188681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130261 q = 1) (hb : d188570 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130261, d188570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45230 q ha hb
    | true =>
      simp only [d130261, d188570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45233 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130279 q = 1) (hb : d188589 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130279, d188589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130279, d188589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45236 q ha hb
  have h3 (q : Pattern) (ha : d130280 q = 1) (hb : d188590 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130280, d188590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130280, d188590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130298 q = 1) (hb : d188617 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130298, d188617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130298, d188617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45239 q ha hb
  have h5 (q : Pattern) (ha : d130299 q = 1) (hb : d188618 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130299, d188618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130299, d188618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130300 q = 1) (hb : d188619 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130300, d188619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130300, d188619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130318 q = 1) (hb : d188646 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130318, d188646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130318, d188646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45242 q ha hb
  have h8 (q : Pattern) (ha : d130319 q = 1) (hb : d188647 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130319, d188647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130319, d188647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130320 q = 1) (hb : d188648 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130320, d188648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130320, d188648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130321 q = 1) (hb : d188649 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130321, d188649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130321, d188649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130339 q = 1) (hb : d188676 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130339, d188676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130339, d188676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45245 q ha hb
  have h12 (q : Pattern) (ha : d130340 q = 1) (hb : d188677 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130340, d188677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130340, d188677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130341 q = 1) (hb : d188678 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130341, d188678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130341, d188678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130342 q = 1) (hb : d188679 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130342, d188679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130342, d188679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130343 q = 1) (hb : d188680 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130343, d188680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130343, d188680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130344 q = 1) (hb : d188681 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130344, d188681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130344, d188681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro45247 (p : Pattern) (ha : d130350 p = 1) (hb : d188687 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130345 q = 1) (hb : d188682 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130345, d188682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45246 q ha hb
    | true =>
      simp only [d130345, d188682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d130346 q = 1) (hb : d188683 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130346, d188683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130346, d188683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130347 q = 1) (hb : d188684 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130347, d188684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130347, d188684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130348 q = 1) (hb : d188685 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130348, d188685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130348, d188685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130349 q = 1) (hb : d188686 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130349, d188686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130349, d188686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130350 q = 1) (hb : d188687 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130350, d188687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130350, d188687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45248 (p : Pattern) (ha : d130356 p = 1) (hb : d188693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130351 q = 1) (hb : d188688 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130351, d188688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45247 q ha hb
    | true =>
      simp only [d130351, d188688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d130352 q = 1) (hb : d188689 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130352, d188689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130352, d188689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130353 q = 1) (hb : d188690 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130353, d188690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130353, d188690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130354 q = 1) (hb : d188691 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130354, d188691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130354, d188691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130355 q = 1) (hb : d188692 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130355, d188692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130355, d188692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130356 q = 1) (hb : d188693 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130356, d188693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130356, d188693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro45249 (p : Pattern) (ha : d130362 p = 1) (hb : d188699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130357 q = 1) (hb : d188694 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130357, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45248 q ha hb
    | true =>
      simp only [d130357, d188694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d130358 q = 1) (hb : d188695 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130358, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130358, d188695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130359 q = 1) (hb : d188696 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130359, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130359, d188696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130360 q = 1) (hb : d188697 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130360, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130360, d188697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130361 q = 1) (hb : d188698 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130361, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130361, d188698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130362 q = 1) (hb : d188699 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130362, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130362, d188699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
