import NetHack.Soko22Hazard87.AndIntroBlocks0430
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro107750 (p : Pattern) (ha : d379618 p = 1) (hb : d379665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379613 q = 1) (hb : d379660 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379613, d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107749 q ha hb
    | true =>
      simp only [d379613, d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379614 q = 1) (hb : d379661 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379614, d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379614, d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379615 q = 1) (hb : d379662 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379615, d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379615, d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379616 q = 1) (hb : d379663 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379616, d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379616, d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379617 q = 1) (hb : d379664 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379617, d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379617, d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379618 q = 1) (hb : d379665 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379618, d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379618, d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107751 (p : Pattern) (ha : d379624 p = 1) (hb : d379671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379619 q = 1) (hb : d379666 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379619, d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107750 q ha hb
    | true =>
      simp only [d379619, d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379620 q = 1) (hb : d379667 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379620, d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379620, d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379621 q = 1) (hb : d379668 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379621, d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379621, d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379622 q = 1) (hb : d379669 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379622, d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379622, d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379623 q = 1) (hb : d379670 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379623, d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379623, d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379624 q = 1) (hb : d379671 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379624, d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379624, d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107752 (p : Pattern) (ha : d379630 p = 1) (hb : d379677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379625 q = 1) (hb : d379672 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379625, d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107751 q ha hb
    | true =>
      simp only [d379625, d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379626 q = 1) (hb : d379673 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379626, d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379626, d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379627 q = 1) (hb : d379674 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379627, d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379627, d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379628 q = 1) (hb : d379675 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379628, d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379628, d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379629 q = 1) (hb : d379676 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379629, d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379629, d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379630 q = 1) (hb : d379677 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379630, d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379630, d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107753 (p : Pattern) (ha : d379373 p = 1) (hb : d379581 p = 1) : d379682 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d367652 q = 1) : d367652 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d364936 q = 1) (hb : d367680 q = 1) : d379678 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d364936, d367680, d379678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d364936, d367680, d379678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379370 q = 1) (hb : d379581 q = 1) : d379679 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379370, d379581, d379679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d379370, d379581, d379679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379581 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379371 q = 1) (hb : d379581 q = 1) : d379680 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379371, d379680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379371, d379680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379372 q = 1) (hb : d379581 q = 1) : d379681 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379372, d379681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379372, d379681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379373 q = 1) (hb : d379581 q = 1) : d379682 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379373, d379682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379373, d379682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro107754 (p : Pattern) (ha : d379379 p = 1) (hb : d379581 p = 1) : d379688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379374 q = 1) (hb : d379581 q = 1) : d379683 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379374, d379683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107753 q ha hb
    | true =>
      simp only [d379374, d379683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379375 q = 1) (hb : d379581 q = 1) : d379684 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379375, d379684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379375, d379684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379376 q = 1) (hb : d379581 q = 1) : d379685 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379376, d379685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379376, d379685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379377 q = 1) (hb : d379581 q = 1) : d379686 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379377, d379686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379377, d379686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379378 q = 1) (hb : d379581 q = 1) : d379687 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379378, d379687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379378, d379687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379379 q = 1) (hb : d379581 q = 1) : d379688 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379379, d379688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379379, d379688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107755 (p : Pattern) (ha : d379385 p = 1) (hb : d379583 p = 1) : d379694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379380 q = 1) (hb : d379582 q = 1) : d379689 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379380, d379582, d379689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107754 q ha hb
    | true =>
      simp only [d379380, d379582, d379689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379381 q = 1) (hb : d379583 q = 1) : d379690 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379381, d379583, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379381, d379583, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379382 q = 1) (hb : d379583 q = 1) : d379691 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379382, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379382, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d379383 q = 1) (hb : d379583 q = 1) : d379692 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379383, d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379383, d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d379384 q = 1) (hb : d379583 q = 1) : d379693 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379384, d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379384, d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d379385 q = 1) (hb : d379583 q = 1) : d379694 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379385, d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379385, d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro107756 (p : Pattern) (ha : d379391 p = 1) (hb : d379583 p = 1) : d379700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379386 q = 1) (hb : d379583 q = 1) : d379695 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379386, d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107755 q ha hb
    | true =>
      simp only [d379386, d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379387 q = 1) (hb : d379583 q = 1) : d379696 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379387, d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379387, d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379388 q = 1) (hb : d379583 q = 1) : d379697 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379388, d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379388, d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379389 q = 1) (hb : d379583 q = 1) : d379698 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379389, d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379389, d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379390 q = 1) (hb : d379583 q = 1) : d379699 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379390, d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379390, d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379391 q = 1) (hb : d379583 q = 1) : d379700 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379391, d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379391, d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107757 (p : Pattern) (ha : d379397 p = 1) (hb : d379583 p = 1) : d379706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379392 q = 1) (hb : d379583 q = 1) : d379701 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379392, d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107756 q ha hb
    | true =>
      simp only [d379392, d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379393 q = 1) (hb : d379583 q = 1) : d379702 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379393, d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379393, d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379394 q = 1) (hb : d379583 q = 1) : d379703 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379394, d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379394, d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379395 q = 1) (hb : d379583 q = 1) : d379704 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379395, d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379395, d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379396 q = 1) (hb : d379583 q = 1) : d379705 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379396, d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379396, d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379397 q = 1) (hb : d379583 q = 1) : d379706 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379397, d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379397, d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107758 (p : Pattern) (ha : d379403 p = 1) (hb : d379583 p = 1) : d379712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379398 q = 1) (hb : d379583 q = 1) : d379707 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379398, d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107757 q ha hb
    | true =>
      simp only [d379398, d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379399 q = 1) (hb : d379583 q = 1) : d379708 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379399, d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379399, d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379400 q = 1) (hb : d379583 q = 1) : d379709 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379400, d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379400, d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379401 q = 1) (hb : d379583 q = 1) : d379710 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379401, d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379401, d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379402 q = 1) (hb : d379583 q = 1) : d379711 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379402, d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379402, d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379403 q = 1) (hb : d379583 q = 1) : d379712 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379403, d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379403, d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107759 (p : Pattern) (ha : d379409 p = 1) (hb : d379583 p = 1) : d379718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379404 q = 1) (hb : d379583 q = 1) : d379713 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379404, d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107758 q ha hb
    | true =>
      simp only [d379404, d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379405 q = 1) (hb : d379583 q = 1) : d379714 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379405, d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379405, d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379406 q = 1) (hb : d379583 q = 1) : d379715 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379406, d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379406, d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379407 q = 1) (hb : d379583 q = 1) : d379716 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379407, d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379407, d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379408 q = 1) (hb : d379583 q = 1) : d379717 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379408, d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379408, d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379409 q = 1) (hb : d379583 q = 1) : d379718 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379409, d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379409, d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107760 (p : Pattern) (ha : d379415 p = 1) (hb : d379583 p = 1) : d379724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379410 q = 1) (hb : d379583 q = 1) : d379719 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379410, d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107759 q ha hb
    | true =>
      simp only [d379410, d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379411 q = 1) (hb : d379583 q = 1) : d379720 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379411, d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379411, d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379412 q = 1) (hb : d379583 q = 1) : d379721 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379412, d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379412, d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379413 q = 1) (hb : d379583 q = 1) : d379722 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379413, d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379413, d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379414 q = 1) (hb : d379583 q = 1) : d379723 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379414, d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379414, d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379415 q = 1) (hb : d379583 q = 1) : d379724 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379415, d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379415, d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107761 (p : Pattern) (ha : d379588 p = 1) (hb : d379682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105144 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379584 q = 1) (hb : d379678 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d379584, d379678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d379584, d379678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d379585 q = 1) (hb : d379679 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379585, d379679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379585, d379679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d379586 q = 1) (hb : d379680 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379586, d379680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379586, d379680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h5 (q : Pattern) (ha : d379587 q = 1) (hb : d379681 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379587, d379681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379587, d379681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d379588 q = 1) (hb : d379682 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379588, d379682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379588, d379682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h6 p ha hb
theorem andIntro107762 (p : Pattern) (ha : d379594 p = 1) (hb : d379688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379589 q = 1) (hb : d379683 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379589, d379683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107761 q ha hb
    | true =>
      simp only [d379589, d379683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379590 q = 1) (hb : d379684 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379590, d379684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379590, d379684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379591 q = 1) (hb : d379685 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379591, d379685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379591, d379685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379592 q = 1) (hb : d379686 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379592, d379686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379592, d379686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379593 q = 1) (hb : d379687 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379593, d379687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379593, d379687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379594 q = 1) (hb : d379688 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379594, d379688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379594, d379688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107763 (p : Pattern) (ha : d379600 p = 1) (hb : d379694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379595 q = 1) (hb : d379689 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379595, d379689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107762 q ha hb
    | true =>
      simp only [d379595, d379689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379596 q = 1) (hb : d379690 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379596, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379596, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379597 q = 1) (hb : d379691 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379597, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379597, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379598 q = 1) (hb : d379692 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379598, d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379598, d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379599 q = 1) (hb : d379693 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379599, d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379599, d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379600 q = 1) (hb : d379694 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379600, d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379600, d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107764 (p : Pattern) (ha : d379606 p = 1) (hb : d379700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379601 q = 1) (hb : d379695 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379601, d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107763 q ha hb
    | true =>
      simp only [d379601, d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379602 q = 1) (hb : d379696 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379602, d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379602, d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379603 q = 1) (hb : d379697 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379603, d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379603, d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379604 q = 1) (hb : d379698 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379604, d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379604, d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379605 q = 1) (hb : d379699 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379605, d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379605, d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379606 q = 1) (hb : d379700 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379606, d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379606, d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107765 (p : Pattern) (ha : d379612 p = 1) (hb : d379706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379607 q = 1) (hb : d379701 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379607, d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107764 q ha hb
    | true =>
      simp only [d379607, d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379608 q = 1) (hb : d379702 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379608, d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379608, d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379609 q = 1) (hb : d379703 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379609, d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379609, d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379610 q = 1) (hb : d379704 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379610, d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379610, d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379611 q = 1) (hb : d379705 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379611, d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379611, d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379612 q = 1) (hb : d379706 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379612, d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379612, d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107766 (p : Pattern) (ha : d379618 p = 1) (hb : d379712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379613 q = 1) (hb : d379707 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379613, d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107765 q ha hb
    | true =>
      simp only [d379613, d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379614 q = 1) (hb : d379708 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379614, d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379614, d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379615 q = 1) (hb : d379709 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379615, d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379615, d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379616 q = 1) (hb : d379710 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379616, d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379616, d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379617 q = 1) (hb : d379711 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379617, d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379617, d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379618 q = 1) (hb : d379712 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379618, d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379618, d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107767 (p : Pattern) (ha : d379624 p = 1) (hb : d379718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379619 q = 1) (hb : d379713 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379619, d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107766 q ha hb
    | true =>
      simp only [d379619, d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379620 q = 1) (hb : d379714 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379620, d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379620, d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379621 q = 1) (hb : d379715 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379621, d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379621, d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379622 q = 1) (hb : d379716 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379622, d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379622, d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379623 q = 1) (hb : d379717 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379623, d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379623, d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379624 q = 1) (hb : d379718 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379624, d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379624, d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107768 (p : Pattern) (ha : d379630 p = 1) (hb : d379724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379625 q = 1) (hb : d379719 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379625, d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107767 q ha hb
    | true =>
      simp only [d379625, d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379626 q = 1) (hb : d379720 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379626, d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379626, d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379627 q = 1) (hb : d379721 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379627, d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379627, d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379628 q = 1) (hb : d379722 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379628, d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379628, d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379629 q = 1) (hb : d379723 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379629, d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379629, d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379630 q = 1) (hb : d379724 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379630, d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379630, d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107769 (p : Pattern) (ha : d379635 p = 1) (hb : d379682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d322122 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105176 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379631 q = 1) (hb : d379678 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d379631, d379678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d379631, d379678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d379632 q = 1) (hb : d379679 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379632, d379679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379632, d379679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d379633 q = 1) (hb : d379680 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379633, d379680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379633, d379680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d379634 q = 1) (hb : d379681 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379634, d379681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379634, d379681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d379635 q = 1) (hb : d379682 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379635, d379682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379635, d379682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h6 p ha hb
theorem andIntro107770 (p : Pattern) (ha : d379641 p = 1) (hb : d379688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379636 q = 1) (hb : d379683 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379636, d379683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107769 q ha hb
    | true =>
      simp only [d379636, d379683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379637 q = 1) (hb : d379684 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379637, d379684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379637, d379684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379638 q = 1) (hb : d379685 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379638, d379685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379638, d379685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379639 q = 1) (hb : d379686 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379639, d379686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379639, d379686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379640 q = 1) (hb : d379687 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379640, d379687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379640, d379687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379641 q = 1) (hb : d379688 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379641, d379688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379641, d379688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107771 (p : Pattern) (ha : d379647 p = 1) (hb : d379694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379642 q = 1) (hb : d379689 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379642, d379689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107770 q ha hb
    | true =>
      simp only [d379642, d379689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379643 q = 1) (hb : d379690 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379643, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379643, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379644 q = 1) (hb : d379691 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379644, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379644, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379645 q = 1) (hb : d379692 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379645, d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379645, d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379646 q = 1) (hb : d379693 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379646, d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379646, d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379647 q = 1) (hb : d379694 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379647, d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379647, d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107772 (p : Pattern) (ha : d379653 p = 1) (hb : d379700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379648 q = 1) (hb : d379695 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379648, d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107771 q ha hb
    | true =>
      simp only [d379648, d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379649 q = 1) (hb : d379696 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379649, d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379649, d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379650 q = 1) (hb : d379697 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379650, d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379650, d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379651 q = 1) (hb : d379698 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379651, d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379651, d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379652 q = 1) (hb : d379699 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379652, d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379652, d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379653 q = 1) (hb : d379700 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379653, d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379653, d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107773 (p : Pattern) (ha : d379659 p = 1) (hb : d379706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379654 q = 1) (hb : d379701 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379654, d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107772 q ha hb
    | true =>
      simp only [d379654, d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379655 q = 1) (hb : d379702 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379655, d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379655, d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379656 q = 1) (hb : d379703 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379656, d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379656, d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379657 q = 1) (hb : d379704 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379657, d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379657, d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379658 q = 1) (hb : d379705 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379658, d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379658, d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379659 q = 1) (hb : d379706 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379659, d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379659, d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107774 (p : Pattern) (ha : d379665 p = 1) (hb : d379712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379660 q = 1) (hb : d379707 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379660, d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107773 q ha hb
    | true =>
      simp only [d379660, d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379661 q = 1) (hb : d379708 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379661, d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379661, d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379662 q = 1) (hb : d379709 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379662, d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379662, d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379663 q = 1) (hb : d379710 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379663, d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379663, d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379664 q = 1) (hb : d379711 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379664, d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379664, d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379665 q = 1) (hb : d379712 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379665, d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379665, d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107775 (p : Pattern) (ha : d379671 p = 1) (hb : d379718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379666 q = 1) (hb : d379713 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379666, d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107774 q ha hb
    | true =>
      simp only [d379666, d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379667 q = 1) (hb : d379714 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379667, d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379667, d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379668 q = 1) (hb : d379715 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379668, d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379668, d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379669 q = 1) (hb : d379716 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379669, d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379669, d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379670 q = 1) (hb : d379717 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379670, d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379670, d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379671 q = 1) (hb : d379718 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379671, d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379671, d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107776 (p : Pattern) (ha : d379677 p = 1) (hb : d379724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379672 q = 1) (hb : d379719 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379672, d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107775 q ha hb
    | true =>
      simp only [d379672, d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379673 q = 1) (hb : d379720 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379673, d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379673, d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379674 q = 1) (hb : d379721 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379674, d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379674, d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379675 q = 1) (hb : d379722 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379675, d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379675, d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379676 q = 1) (hb : d379723 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379676, d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379676, d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379677 q = 1) (hb : d379724 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379677, d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379677, d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107777 (p : Pattern) (ha : d379339 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379333 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379731 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379334 q = 1) (hb : d379732 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379334, d379732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379334, d379732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379335 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379335, d379733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379335, d379733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379336 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379337 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379338 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d379339 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro107778 (p : Pattern) (ha : d379345 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379340 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107777 q ha hb
    | true =>
      simp only [d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379341 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379342 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379343 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379344 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379345 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107779 (p : Pattern) (ha : d379351 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379346 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107778 q ha hb
    | true =>
      simp only [d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379347 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379348 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379349 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379350 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379351 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107780 (p : Pattern) (ha : d379357 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379352 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107779 q ha hb
    | true =>
      simp only [d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379353 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379354 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379355 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379356 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379357 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107781 (p : Pattern) (ha : d379363 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379358 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107780 q ha hb
    | true =>
      simp only [d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379359 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379360 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379361 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379362 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379363 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107782 (p : Pattern) (ha : d379369 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379364 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107781 q ha hb
    | true =>
      simp only [d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379365 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379366 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379367 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379368 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379369 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107783 (p : Pattern) (ha : d0 p = 1) (hb : d379825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379825 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107784 (p : Pattern) (ha : d379385 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379379 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379731 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379380 q = 1) (hb : d379732 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379380, d379732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379380, d379732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379381 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379381, d379733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379381, d379733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379382 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379383 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379384 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d379385 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro107785 (p : Pattern) (ha : d379391 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379386 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107784 q ha hb
    | true =>
      simp only [d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379387 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379388 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379389 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379390 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379391 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107786 (p : Pattern) (ha : d379397 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379392 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107785 q ha hb
    | true =>
      simp only [d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379393 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379394 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379395 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379396 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379397 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107787 (p : Pattern) (ha : d379403 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379398 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107786 q ha hb
    | true =>
      simp only [d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379399 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379400 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379401 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379402 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379403 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107788 (p : Pattern) (ha : d379409 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379404 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107787 q ha hb
    | true =>
      simp only [d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379405 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379406 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379407 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379408 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379409 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107789 (p : Pattern) (ha : d379415 p = 1) (hb : d379733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379410 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107788 q ha hb
    | true =>
      simp only [d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379411 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379412 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379413 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379414 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379415 q = 1) (hb : d379733 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107790 (p : Pattern) (ha : d0 p = 1) (hb : d379871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379871 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107791 (p : Pattern) (ha : d379339 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379333 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379873 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379334 q = 1) (hb : d379874 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379334, d379874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379334, d379874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379335 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379335, d379875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379335, d379875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379336 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379337 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379338 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d379339 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro107792 (p : Pattern) (ha : d379345 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379340 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107791 q ha hb
    | true =>
      simp only [d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379341 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379342 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379343 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379344 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379345 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107793 (p : Pattern) (ha : d379351 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379346 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107792 q ha hb
    | true =>
      simp only [d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379347 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379348 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379349 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379350 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379351 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107794 (p : Pattern) (ha : d379357 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379352 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107793 q ha hb
    | true =>
      simp only [d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379353 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379354 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379355 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379356 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379357 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107795 (p : Pattern) (ha : d379363 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379358 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107794 q ha hb
    | true =>
      simp only [d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379359 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379360 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379361 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379362 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379363 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107796 (p : Pattern) (ha : d379369 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379364 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107795 q ha hb
    | true =>
      simp only [d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379365 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379366 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379367 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379368 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379369 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107797 (p : Pattern) (ha : d379385 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379379 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379873 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379380 q = 1) (hb : d379874 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379380, d379874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379380, d379874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379381 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379381, d379875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379381, d379875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379382 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379383 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379384 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d379385 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro107798 (p : Pattern) (ha : d379391 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379386 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107797 q ha hb
    | true =>
      simp only [d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379387 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379388 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379389 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379390 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379391 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107799 (p : Pattern) (ha : d379397 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379392 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107798 q ha hb
    | true =>
      simp only [d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379393 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379394 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379395 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379396 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379397 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107800 (p : Pattern) (ha : d379403 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379398 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107799 q ha hb
    | true =>
      simp only [d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379399 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379400 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379401 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379402 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379403 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107801 (p : Pattern) (ha : d379409 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379404 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107800 q ha hb
    | true =>
      simp only [d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379405 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379406 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379407 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379408 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379409 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107802 (p : Pattern) (ha : d379415 p = 1) (hb : d379875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379410 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107801 q ha hb
    | true =>
      simp only [d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379411 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379412 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379413 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379414 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379415 q = 1) (hb : d379875 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107803 (p : Pattern) (ha : d379277 p = 1) (hb : d379369 p = 1) : d379369 p = 1 := by
  have h0 (q : Pattern) (ha : d379277 q = 1) (hb : d379369 q = 1) : d379369 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro107804 (p : Pattern) (ha : d378994 p = 1) (hb : d379327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d322122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105010 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d322162 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105062 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d322163 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319888 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319889 q = 1) (hb : d379324 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d379324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d379324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d378992 q = 1) (hb : d379325 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d378992, d379325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d378992, d379325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d378993 q = 1) (hb : d379326 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d378993, d379326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d378993, d379326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d378994 q = 1) (hb : d379327 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d378994, d379327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d378994, d379327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro107805 (p : Pattern) (ha : d379000 p = 1) (hb : d379333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d378995 q = 1) (hb : d379328 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d378995, d379328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107804 q ha hb
    | true =>
      simp only [d378995, d379328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d378996 q = 1) (hb : d379329 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d378996, d379329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d378996, d379329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d378997 q = 1) (hb : d379330 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d378997, d379330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d378997, d379330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d378998 q = 1) (hb : d379331 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d378998, d379331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d378998, d379331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d378999 q = 1) (hb : d379332 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d378999, d379332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d378999, d379332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379000 q = 1) (hb : d379333 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379000, d379333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379000, d379333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107806 (p : Pattern) (ha : d379006 p = 1) (hb : d379339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379001 q = 1) (hb : d379334 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379001, d379334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107805 q ha hb
    | true =>
      simp only [d379001, d379334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379002 q = 1) (hb : d379335 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379002, d379335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379002, d379335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379003 q = 1) (hb : d379336 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379003, d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379003, d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379004 q = 1) (hb : d379337 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379004, d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379004, d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379005 q = 1) (hb : d379338 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379005, d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379005, d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379006 q = 1) (hb : d379339 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379006, d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379006, d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107807 (p : Pattern) (ha : d379012 p = 1) (hb : d379345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379007 q = 1) (hb : d379340 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379007, d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107806 q ha hb
    | true =>
      simp only [d379007, d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379008 q = 1) (hb : d379341 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379008, d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379008, d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379009 q = 1) (hb : d379342 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379009, d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379009, d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379010 q = 1) (hb : d379343 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379010, d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379010, d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379011 q = 1) (hb : d379344 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379011, d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379011, d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379012 q = 1) (hb : d379345 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379012, d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379012, d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107808 (p : Pattern) (ha : d379018 p = 1) (hb : d379351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379013 q = 1) (hb : d379346 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379013, d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107807 q ha hb
    | true =>
      simp only [d379013, d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379014 q = 1) (hb : d379347 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379014, d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379014, d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379015 q = 1) (hb : d379348 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379015, d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379015, d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379016 q = 1) (hb : d379349 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379016, d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379016, d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379017 q = 1) (hb : d379350 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379017, d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379017, d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379018 q = 1) (hb : d379351 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379018, d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379018, d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107809 (p : Pattern) (ha : d379024 p = 1) (hb : d379357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379019 q = 1) (hb : d379352 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379019, d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107808 q ha hb
    | true =>
      simp only [d379019, d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379020 q = 1) (hb : d379353 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379020, d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379020, d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379021 q = 1) (hb : d379354 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379021, d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379021, d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379022 q = 1) (hb : d379355 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379022, d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379022, d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379023 q = 1) (hb : d379356 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379023, d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379023, d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379024 q = 1) (hb : d379357 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379024, d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379024, d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107810 (p : Pattern) (ha : d379030 p = 1) (hb : d379363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379025 q = 1) (hb : d379358 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379025, d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107809 q ha hb
    | true =>
      simp only [d379025, d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379026 q = 1) (hb : d379359 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379026, d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379026, d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379027 q = 1) (hb : d379360 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379027, d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379027, d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379028 q = 1) (hb : d379361 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379028, d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379028, d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379029 q = 1) (hb : d379362 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379029, d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379029, d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379030 q = 1) (hb : d379363 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379030, d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379030, d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107811 (p : Pattern) (ha : d379036 p = 1) (hb : d379369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379031 q = 1) (hb : d379364 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379031, d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107810 q ha hb
    | true =>
      simp only [d379031, d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379032 q = 1) (hb : d379365 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379032, d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379032, d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379033 q = 1) (hb : d379366 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379033, d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379033, d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379034 q = 1) (hb : d379367 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379034, d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379034, d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379035 q = 1) (hb : d379368 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379035, d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379035, d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379036 q = 1) (hb : d379369 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379036, d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379036, d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107812 (p : Pattern) (ha : d379277 p = 1) (hb : d379415 p = 1) : d379415 p = 1 := by
  have h0 (q : Pattern) (ha : d379277 q = 1) (hb : d379415 q = 1) : d379415 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro107813 (p : Pattern) (ha : d378994 p = 1) (hb : d379373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105144 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105150 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d319888 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d319889 q = 1) (hb : d379370 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d379370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d379370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d378992 q = 1) (hb : d379371 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d378992, d379371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d378992, d379371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d378993 q = 1) (hb : d379372 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d378993, d379372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d378993, d379372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d378994 q = 1) (hb : d379373 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d378994, d379373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d378994, d379373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro107814 (p : Pattern) (ha : d379000 p = 1) (hb : d379379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d378995 q = 1) (hb : d379374 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d378995, d379374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107813 q ha hb
    | true =>
      simp only [d378995, d379374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d378996 q = 1) (hb : d379375 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d378996, d379375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d378996, d379375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d378997 q = 1) (hb : d379376 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d378997, d379376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d378997, d379376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d378998 q = 1) (hb : d379377 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d378998, d379377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d378998, d379377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d378999 q = 1) (hb : d379378 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d378999, d379378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d378999, d379378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379000 q = 1) (hb : d379379 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379000, d379379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379000, d379379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107815 (p : Pattern) (ha : d379006 p = 1) (hb : d379385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379001 q = 1) (hb : d379380 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379001, d379380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107814 q ha hb
    | true =>
      simp only [d379001, d379380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379002 q = 1) (hb : d379381 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379002, d379381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379002, d379381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379003 q = 1) (hb : d379382 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379003, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379003, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379004 q = 1) (hb : d379383 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379004, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379004, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379005 q = 1) (hb : d379384 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379005, d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379005, d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379006 q = 1) (hb : d379385 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379006, d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379006, d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107816 (p : Pattern) (ha : d379012 p = 1) (hb : d379391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379007 q = 1) (hb : d379386 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379007, d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107815 q ha hb
    | true =>
      simp only [d379007, d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379008 q = 1) (hb : d379387 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379008, d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379008, d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379009 q = 1) (hb : d379388 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379009, d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379009, d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379010 q = 1) (hb : d379389 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379010, d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379010, d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379011 q = 1) (hb : d379390 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379011, d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379011, d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379012 q = 1) (hb : d379391 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379012, d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379012, d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107817 (p : Pattern) (ha : d379018 p = 1) (hb : d379397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379013 q = 1) (hb : d379392 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379013, d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107816 q ha hb
    | true =>
      simp only [d379013, d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379014 q = 1) (hb : d379393 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379014, d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379014, d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379015 q = 1) (hb : d379394 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379015, d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379015, d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379016 q = 1) (hb : d379395 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379016, d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379016, d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379017 q = 1) (hb : d379396 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379017, d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379017, d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379018 q = 1) (hb : d379397 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379018, d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379018, d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107818 (p : Pattern) (ha : d379024 p = 1) (hb : d379403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379019 q = 1) (hb : d379398 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379019, d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107817 q ha hb
    | true =>
      simp only [d379019, d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379020 q = 1) (hb : d379399 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379020, d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379020, d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379021 q = 1) (hb : d379400 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379021, d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379021, d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379022 q = 1) (hb : d379401 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379022, d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379022, d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379023 q = 1) (hb : d379402 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379023, d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379023, d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379024 q = 1) (hb : d379403 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379024, d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379024, d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107819 (p : Pattern) (ha : d379030 p = 1) (hb : d379409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379025 q = 1) (hb : d379404 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379025, d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107818 q ha hb
    | true =>
      simp only [d379025, d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379026 q = 1) (hb : d379405 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379026, d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379026, d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379027 q = 1) (hb : d379406 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379027, d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379027, d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379028 q = 1) (hb : d379407 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379028, d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379028, d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379029 q = 1) (hb : d379408 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379029, d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379029, d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379030 q = 1) (hb : d379409 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379030, d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379030, d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107820 (p : Pattern) (ha : d379036 p = 1) (hb : d379415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379031 q = 1) (hb : d379410 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379031, d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107819 q ha hb
    | true =>
      simp only [d379031, d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379032 q = 1) (hb : d379411 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379032, d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379032, d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379033 q = 1) (hb : d379412 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379033, d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379033, d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379034 q = 1) (hb : d379413 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379034, d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379034, d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379035 q = 1) (hb : d379414 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379035, d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379035, d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379036 q = 1) (hb : d379415 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379036, d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379036, d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107821 (p : Pattern) (ha : d379039 p = 1) (hb : d379373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d322122 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105176 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322162 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105182 q ha hb
  have h3 (q : Pattern) (ha : d322163 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d322204 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322205 q = 1) (hb : d379370 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d322205, d379370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322205, d379370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d379037 q = 1) (hb : d379371 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379037, d379371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379037, d379371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d379038 q = 1) (hb : d379372 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379038, d379372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379038, d379372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d379039 q = 1) (hb : d379373 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379039, d379373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379039, d379373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro107822 (p : Pattern) (ha : d379045 p = 1) (hb : d379379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379040 q = 1) (hb : d379374 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379040, d379374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107821 q ha hb
    | true =>
      simp only [d379040, d379374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379041 q = 1) (hb : d379375 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379041, d379375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379041, d379375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379042 q = 1) (hb : d379376 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379042, d379376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379042, d379376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379043 q = 1) (hb : d379377 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379043, d379377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379043, d379377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379044 q = 1) (hb : d379378 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379044, d379378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379044, d379378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379045 q = 1) (hb : d379379 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379045, d379379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379045, d379379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107823 (p : Pattern) (ha : d379051 p = 1) (hb : d379385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379046 q = 1) (hb : d379380 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379046, d379380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107822 q ha hb
    | true =>
      simp only [d379046, d379380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379047 q = 1) (hb : d379381 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379047, d379381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379047, d379381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379048 q = 1) (hb : d379382 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379048, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379048, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379049 q = 1) (hb : d379383 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379049, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379049, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379050 q = 1) (hb : d379384 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379050, d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379050, d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379051 q = 1) (hb : d379385 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379051, d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379051, d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107824 (p : Pattern) (ha : d379057 p = 1) (hb : d379391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379052 q = 1) (hb : d379386 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379052, d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107823 q ha hb
    | true =>
      simp only [d379052, d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379053 q = 1) (hb : d379387 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379053, d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379053, d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379054 q = 1) (hb : d379388 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379054, d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379054, d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379055 q = 1) (hb : d379389 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379055, d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379055, d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379056 q = 1) (hb : d379390 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379056, d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379056, d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379057 q = 1) (hb : d379391 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379057, d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379057, d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107825 (p : Pattern) (ha : d379063 p = 1) (hb : d379397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379058 q = 1) (hb : d379392 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379058, d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107824 q ha hb
    | true =>
      simp only [d379058, d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379059 q = 1) (hb : d379393 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379059, d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379059, d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379060 q = 1) (hb : d379394 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379060, d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379060, d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379061 q = 1) (hb : d379395 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379061, d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379061, d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379062 q = 1) (hb : d379396 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379062, d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379062, d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379063 q = 1) (hb : d379397 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379063, d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379063, d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107826 (p : Pattern) (ha : d379069 p = 1) (hb : d379403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379064 q = 1) (hb : d379398 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379064, d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107825 q ha hb
    | true =>
      simp only [d379064, d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379065 q = 1) (hb : d379399 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379065, d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379065, d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379066 q = 1) (hb : d379400 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379066, d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379066, d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379067 q = 1) (hb : d379401 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379067, d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379067, d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379068 q = 1) (hb : d379402 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379068, d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379068, d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379069 q = 1) (hb : d379403 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379069, d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379069, d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107827 (p : Pattern) (ha : d379075 p = 1) (hb : d379409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379070 q = 1) (hb : d379404 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379070, d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107826 q ha hb
    | true =>
      simp only [d379070, d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379071 q = 1) (hb : d379405 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379071, d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379071, d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379072 q = 1) (hb : d379406 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379072, d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379072, d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379073 q = 1) (hb : d379407 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379073, d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379073, d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379074 q = 1) (hb : d379408 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379074, d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379074, d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379075 q = 1) (hb : d379409 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379075, d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379075, d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107828 (p : Pattern) (ha : d379081 p = 1) (hb : d379415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379076 q = 1) (hb : d379410 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379076, d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107827 q ha hb
    | true =>
      simp only [d379076, d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379077 q = 1) (hb : d379411 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379077, d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379077, d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379078 q = 1) (hb : d379412 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379078, d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379078, d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379079 q = 1) (hb : d379413 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379079, d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379079, d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379080 q = 1) (hb : d379414 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379080, d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379080, d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379081 q = 1) (hb : d379415 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379081, d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379081, d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107829 (p : Pattern) (ha : d379339 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379880 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379336 q = 1) (hb : d379881 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379336, d379881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379336, d379881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379337 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379337, d379882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379337, d379882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379338 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379339 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro107830 (p : Pattern) (ha : d379345 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379340 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107829 q ha hb
    | true =>
      simp only [d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379341 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379342 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379343 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379344 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379345 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107831 (p : Pattern) (ha : d379351 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379346 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107830 q ha hb
    | true =>
      simp only [d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379347 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379348 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379349 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379350 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379351 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107832 (p : Pattern) (ha : d379357 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379352 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107831 q ha hb
    | true =>
      simp only [d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379353 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379354 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379355 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379356 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379357 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107833 (p : Pattern) (ha : d379363 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379358 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107832 q ha hb
    | true =>
      simp only [d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379359 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379360 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379361 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379362 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379363 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107834 (p : Pattern) (ha : d379369 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379364 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107833 q ha hb
    | true =>
      simp only [d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379365 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379366 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379367 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379368 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379369 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107835 (p : Pattern) (ha : d0 p = 1) (hb : d379966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379966 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107836 (p : Pattern) (ha : d379385 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379880 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379382 q = 1) (hb : d379881 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379382, d379881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379382, d379881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379383 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379383, d379882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379383, d379882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379384 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379385 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro107837 (p : Pattern) (ha : d379391 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379386 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107836 q ha hb
    | true =>
      simp only [d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379387 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379388 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379389 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379390 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379391 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107838 (p : Pattern) (ha : d379397 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379392 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107837 q ha hb
    | true =>
      simp only [d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379393 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379394 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379395 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379396 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379397 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107839 (p : Pattern) (ha : d379403 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379398 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107838 q ha hb
    | true =>
      simp only [d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379399 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379400 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379401 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379402 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379403 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107840 (p : Pattern) (ha : d379409 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379404 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107839 q ha hb
    | true =>
      simp only [d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379405 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379406 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379407 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379408 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379409 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107841 (p : Pattern) (ha : d379415 p = 1) (hb : d379882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379410 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107840 q ha hb
    | true =>
      simp only [d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379411 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379412 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379413 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379414 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379415 q = 1) (hb : d379882 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107842 (p : Pattern) (ha : d0 p = 1) (hb : d380008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380008 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107843 (p : Pattern) (ha : d379271 p = 1) (hb : d379339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379270 q = 1) (hb : d379336 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379270, d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d379270, d379336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379337 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379271, d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379271, d379337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379338 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d379271 q = 1) (hb : d379339 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h7 p ha hb
theorem andIntro107844 (p : Pattern) (ha : d379271 p = 1) (hb : d379345 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379271 q = 1) (hb : d379340 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107843 q ha hb
    | true =>
      simp only [d379340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379271 q = 1) (hb : d379341 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379271 q = 1) (hb : d379342 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379343 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379271 q = 1) (hb : d379344 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379345 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107845 (p : Pattern) (ha : d379271 p = 1) (hb : d379351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379271 q = 1) (hb : d379346 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107844 q ha hb
    | true =>
      simp only [d379346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379271 q = 1) (hb : d379347 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379271 q = 1) (hb : d379348 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379349 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379271 q = 1) (hb : d379350 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379351 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107846 (p : Pattern) (ha : d379271 p = 1) (hb : d379357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379271 q = 1) (hb : d379352 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107845 q ha hb
    | true =>
      simp only [d379352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379271 q = 1) (hb : d379353 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379271 q = 1) (hb : d379354 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379355 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379271 q = 1) (hb : d379356 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379357 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107847 (p : Pattern) (ha : d379271 p = 1) (hb : d379363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379271 q = 1) (hb : d379358 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107846 q ha hb
    | true =>
      simp only [d379358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379271 q = 1) (hb : d379359 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379271 q = 1) (hb : d379360 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379361 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379271 q = 1) (hb : d379362 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379363 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107848 (p : Pattern) (ha : d379271 p = 1) (hb : d379369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379271 q = 1) (hb : d379364 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107847 q ha hb
    | true =>
      simp only [d379364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379271 q = 1) (hb : d379365 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379271 q = 1) (hb : d379366 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379367 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379271 q = 1) (hb : d379368 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379369 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107849 (p : Pattern) (ha : d379271 p = 1) (hb : d379385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379381 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379270 q = 1) (hb : d379382 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379270, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d379270, d379382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379383 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379271, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379271, d379383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379384 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d379271 q = 1) (hb : d379385 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h7 p ha hb
theorem andIntro107850 (p : Pattern) (ha : d379271 p = 1) (hb : d379391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379271 q = 1) (hb : d379386 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107849 q ha hb
    | true =>
      simp only [d379386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379271 q = 1) (hb : d379387 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379271 q = 1) (hb : d379388 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379389 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379271 q = 1) (hb : d379390 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379391 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107851 (p : Pattern) (ha : d379271 p = 1) (hb : d379397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379271 q = 1) (hb : d379392 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107850 q ha hb
    | true =>
      simp only [d379392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379271 q = 1) (hb : d379393 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379271 q = 1) (hb : d379394 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379395 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379271 q = 1) (hb : d379396 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379397 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107852 (p : Pattern) (ha : d379271 p = 1) (hb : d379403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379271 q = 1) (hb : d379398 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107851 q ha hb
    | true =>
      simp only [d379398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379271 q = 1) (hb : d379399 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379271 q = 1) (hb : d379400 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379401 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379271 q = 1) (hb : d379402 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379403 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107853 (p : Pattern) (ha : d379271 p = 1) (hb : d379409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379271 q = 1) (hb : d379404 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107852 q ha hb
    | true =>
      simp only [d379404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379271 q = 1) (hb : d379405 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379271 q = 1) (hb : d379406 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379407 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379271 q = 1) (hb : d379408 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379409 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107854 (p : Pattern) (ha : d379271 p = 1) (hb : d379415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379271 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379271 q = 1) (hb : d379410 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107853 q ha hb
    | true =>
      simp only [d379410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379271 q = 1) (hb : d379411 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379271 q = 1) (hb : d379412 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379271 q = 1) (hb : d379413 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379271 q = 1) (hb : d379414 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379271 q = 1) (hb : d379415 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107855 (p : Pattern) (ha : d379635 p = 1) (hb : d380012 p = 1) : d380068 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322082 q = 1) : d322082 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322122 q = 1) (hb : d365414 q = 1) : d380063 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d365414, d380063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322122, d365414, d380063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379631 q = 1) (hb : d380012 q = 1) : d380064 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d379631, d380012, d380064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379631, d380012, d380064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d380012 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379632 q = 1) (hb : d380012 q = 1) : d380065 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379632, d380065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379632, d380065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379633 q = 1) (hb : d380012 q = 1) : d380066 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379633, d380066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379633, d380066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379634 q = 1) (hb : d380012 q = 1) : d380067 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379634, d380067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379634, d380067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d379635 q = 1) (hb : d380012 q = 1) : d380068 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379635, d380068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d379635, d380068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro107856 (p : Pattern) (ha : d379641 p = 1) (hb : d380013 p = 1) : d380074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380012 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379636 q = 1) (hb : d380012 q = 1) : d380069 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379636, d380069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107855 q ha hb
    | true =>
      simp only [d379636, d380069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379637 q = 1) (hb : d380012 q = 1) : d380070 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379637, d380070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379637, d380070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379638 q = 1) (hb : d380012 q = 1) : d380071 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379638, d380071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379638, d380071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379639 q = 1) (hb : d380012 q = 1) : d380072 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379639, d380072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379639, d380072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379640 q = 1) (hb : d380012 q = 1) : d380073 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379640, d380073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379640, d380073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d379641 q = 1) (hb : d380013 q = 1) : d380074 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379641, d380013, d380074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379641, d380013, d380074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro107857 (p : Pattern) (ha : d379647 p = 1) (hb : d380014 p = 1) : d380080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379642 q = 1) (hb : d380014 q = 1) : d380075 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379642, d380014, d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107856 q ha hb
    | true =>
      simp only [d379642, d380014, d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379643 q = 1) (hb : d380014 q = 1) : d380076 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379643, d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379643, d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379644 q = 1) (hb : d380014 q = 1) : d380077 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379644, d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379644, d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d379645 q = 1) (hb : d380014 q = 1) : d380078 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379645, d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379645, d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d379646 q = 1) (hb : d380014 q = 1) : d380079 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379646, d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379646, d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d379647 q = 1) (hb : d380014 q = 1) : d380080 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379647, d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379647, d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro107858 (p : Pattern) (ha : d379653 p = 1) (hb : d380014 p = 1) : d380086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379648 q = 1) (hb : d380014 q = 1) : d380081 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379648, d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107857 q ha hb
    | true =>
      simp only [d379648, d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379649 q = 1) (hb : d380014 q = 1) : d380082 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379649, d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379649, d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379650 q = 1) (hb : d380014 q = 1) : d380083 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379650, d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379650, d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379651 q = 1) (hb : d380014 q = 1) : d380084 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379651, d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379651, d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379652 q = 1) (hb : d380014 q = 1) : d380085 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379652, d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379652, d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379653 q = 1) (hb : d380014 q = 1) : d380086 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379653, d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379653, d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107859 (p : Pattern) (ha : d379659 p = 1) (hb : d380014 p = 1) : d380092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379654 q = 1) (hb : d380014 q = 1) : d380087 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379654, d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107858 q ha hb
    | true =>
      simp only [d379654, d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379655 q = 1) (hb : d380014 q = 1) : d380088 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379655, d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379655, d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379656 q = 1) (hb : d380014 q = 1) : d380089 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379656, d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379656, d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379657 q = 1) (hb : d380014 q = 1) : d380090 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379657, d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379657, d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379658 q = 1) (hb : d380014 q = 1) : d380091 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379658, d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379658, d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379659 q = 1) (hb : d380014 q = 1) : d380092 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379659, d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379659, d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107860 (p : Pattern) (ha : d379665 p = 1) (hb : d380014 p = 1) : d380098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379660 q = 1) (hb : d380014 q = 1) : d380093 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379660, d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107859 q ha hb
    | true =>
      simp only [d379660, d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379661 q = 1) (hb : d380014 q = 1) : d380094 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379661, d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379661, d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379662 q = 1) (hb : d380014 q = 1) : d380095 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379662, d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379662, d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379663 q = 1) (hb : d380014 q = 1) : d380096 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379663, d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379663, d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379664 q = 1) (hb : d380014 q = 1) : d380097 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379664, d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379664, d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379665 q = 1) (hb : d380014 q = 1) : d380098 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379665, d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379665, d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107861 (p : Pattern) (ha : d379671 p = 1) (hb : d380014 p = 1) : d380104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379666 q = 1) (hb : d380014 q = 1) : d380099 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379666, d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107860 q ha hb
    | true =>
      simp only [d379666, d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379667 q = 1) (hb : d380014 q = 1) : d380100 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379667, d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379667, d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379668 q = 1) (hb : d380014 q = 1) : d380101 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379668, d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379668, d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379669 q = 1) (hb : d380014 q = 1) : d380102 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379669, d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379669, d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379670 q = 1) (hb : d380014 q = 1) : d380103 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379670, d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379670, d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379671 q = 1) (hb : d380014 q = 1) : d380104 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379671, d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379671, d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107862 (p : Pattern) (ha : d379677 p = 1) (hb : d380014 p = 1) : d380110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379672 q = 1) (hb : d380014 q = 1) : d380105 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379672, d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107861 q ha hb
    | true =>
      simp only [d379672, d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379673 q = 1) (hb : d380014 q = 1) : d380106 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379673, d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379673, d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379674 q = 1) (hb : d380014 q = 1) : d380107 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379674, d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379674, d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379675 q = 1) (hb : d380014 q = 1) : d380108 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379675, d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379675, d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379676 q = 1) (hb : d380014 q = 1) : d380109 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379676, d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379676, d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379677 q = 1) (hb : d380014 q = 1) : d380110 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379677, d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379677, d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107863 (p : Pattern) (ha : d380020 p = 1) (hb : d380068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380015 q = 1) (hb : d380063 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380015, d380063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d380015, d380063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380016 q = 1) (hb : d380064 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380016, d380064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380016, d380064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380017 q = 1) (hb : d380065 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380017, d380065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380017, d380065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380018 q = 1) (hb : d380066 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380018, d380066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380018, d380066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380019 q = 1) (hb : d380067 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380019, d380067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380019, d380067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380020 q = 1) (hb : d380068 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380020, d380068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380020, d380068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107864 (p : Pattern) (ha : d380026 p = 1) (hb : d380074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380021 q = 1) (hb : d380069 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380021, d380069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107863 q ha hb
    | true =>
      simp only [d380021, d380069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380022 q = 1) (hb : d380070 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380022, d380070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380022, d380070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380023 q = 1) (hb : d380071 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380023, d380071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380023, d380071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380024 q = 1) (hb : d380072 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380024, d380072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380024, d380072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380025 q = 1) (hb : d380073 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380025, d380073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380025, d380073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380026 q = 1) (hb : d380074 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380026, d380074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380026, d380074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107865 (p : Pattern) (ha : d380032 p = 1) (hb : d380080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380027 q = 1) (hb : d380075 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380027, d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107864 q ha hb
    | true =>
      simp only [d380027, d380075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380028 q = 1) (hb : d380076 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380028, d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380028, d380076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380029 q = 1) (hb : d380077 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380029, d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380029, d380077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380030 q = 1) (hb : d380078 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380030, d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380030, d380078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380031 q = 1) (hb : d380079 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380031, d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380031, d380079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380032 q = 1) (hb : d380080 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380032, d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380032, d380080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107866 (p : Pattern) (ha : d380038 p = 1) (hb : d380086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380033 q = 1) (hb : d380081 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380033, d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107865 q ha hb
    | true =>
      simp only [d380033, d380081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380034 q = 1) (hb : d380082 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380034, d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380034, d380082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380035 q = 1) (hb : d380083 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380035, d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380035, d380083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380036 q = 1) (hb : d380084 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380036, d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380036, d380084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380037 q = 1) (hb : d380085 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380037, d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380037, d380085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380038 q = 1) (hb : d380086 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380038, d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380038, d380086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107867 (p : Pattern) (ha : d380044 p = 1) (hb : d380092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380039 q = 1) (hb : d380087 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380039, d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107866 q ha hb
    | true =>
      simp only [d380039, d380087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380040 q = 1) (hb : d380088 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380040, d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380040, d380088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380041 q = 1) (hb : d380089 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380041, d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380041, d380089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380042 q = 1) (hb : d380090 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380042, d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380042, d380090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380043 q = 1) (hb : d380091 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380043, d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380043, d380091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380044 q = 1) (hb : d380092 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380044, d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380044, d380092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107868 (p : Pattern) (ha : d380050 p = 1) (hb : d380098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380045 q = 1) (hb : d380093 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380045, d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107867 q ha hb
    | true =>
      simp only [d380045, d380093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380046 q = 1) (hb : d380094 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380046, d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380046, d380094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380047 q = 1) (hb : d380095 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380047, d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380047, d380095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380048 q = 1) (hb : d380096 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380048, d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380048, d380096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380049 q = 1) (hb : d380097 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380049, d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380049, d380097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380050 q = 1) (hb : d380098 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380050, d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380050, d380098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107869 (p : Pattern) (ha : d380056 p = 1) (hb : d380104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380051 q = 1) (hb : d380099 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380051, d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107868 q ha hb
    | true =>
      simp only [d380051, d380099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380052 q = 1) (hb : d380100 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380052, d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380052, d380100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380053 q = 1) (hb : d380101 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380053, d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380053, d380101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380054 q = 1) (hb : d380102 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380054, d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380054, d380102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380055 q = 1) (hb : d380103 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380055, d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380055, d380103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380056 q = 1) (hb : d380104 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380056, d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380056, d380104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107870 (p : Pattern) (ha : d380062 p = 1) (hb : d380110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380057 q = 1) (hb : d380105 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380057, d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107869 q ha hb
    | true =>
      simp only [d380057, d380105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380058 q = 1) (hb : d380106 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380058, d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380058, d380106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380059 q = 1) (hb : d380107 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380059, d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380059, d380107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380060 q = 1) (hb : d380108 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380060, d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380060, d380108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380061 q = 1) (hb : d380109 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380061, d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380061, d380109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380062 q = 1) (hb : d380110 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380062, d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380062, d380110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107871 (p : Pattern) (ha : d379682 p = 1) (hb : d380012 p = 1) : d380116 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d367625 q = 1) : d367625 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d367651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d365414 q = 1) (hb : d367652 q = 1) : d380111 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365414, d367652, d380111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d365414, d367652, d380111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379678 q = 1) (hb : d380012 q = 1) : d380112 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d379678, d380012, d380112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d379678, d380012, d380112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d380012 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379679 q = 1) (hb : d380012 q = 1) : d380113 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379679, d380113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379679, d380113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379680 q = 1) (hb : d380012 q = 1) : d380114 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379680, d380114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379680, d380114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379681 q = 1) (hb : d380012 q = 1) : d380115 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379681, d380115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379681, d380115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d379682 q = 1) (hb : d380012 q = 1) : d380116 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379682, d380116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d379682, d380116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro107872 (p : Pattern) (ha : d379688 p = 1) (hb : d380013 p = 1) : d380122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380012 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379683 q = 1) (hb : d380012 q = 1) : d380117 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379683, d380117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107871 q ha hb
    | true =>
      simp only [d379683, d380117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379684 q = 1) (hb : d380012 q = 1) : d380118 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379684, d380118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379684, d380118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379685 q = 1) (hb : d380012 q = 1) : d380119 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379685, d380119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379685, d380119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379686 q = 1) (hb : d380012 q = 1) : d380120 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379686, d380120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379686, d380120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379687 q = 1) (hb : d380012 q = 1) : d380121 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379687, d380121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379687, d380121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d379688 q = 1) (hb : d380013 q = 1) : d380122 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379688, d380013, d380122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379688, d380013, d380122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro107873 (p : Pattern) (ha : d379694 p = 1) (hb : d380014 p = 1) : d380128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379689 q = 1) (hb : d380014 q = 1) : d380123 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379689, d380014, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107872 q ha hb
    | true =>
      simp only [d379689, d380014, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379690 q = 1) (hb : d380014 q = 1) : d380124 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379690, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379690, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379691 q = 1) (hb : d380014 q = 1) : d380125 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379691, d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379691, d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d379692 q = 1) (hb : d380014 q = 1) : d380126 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379692, d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379692, d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d379693 q = 1) (hb : d380014 q = 1) : d380127 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379693, d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379693, d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d379694 q = 1) (hb : d380014 q = 1) : d380128 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379694, d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379694, d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro107874 (p : Pattern) (ha : d379700 p = 1) (hb : d380014 p = 1) : d380134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379695 q = 1) (hb : d380014 q = 1) : d380129 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379695, d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107873 q ha hb
    | true =>
      simp only [d379695, d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379696 q = 1) (hb : d380014 q = 1) : d380130 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379696, d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379696, d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379697 q = 1) (hb : d380014 q = 1) : d380131 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379697, d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379697, d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379698 q = 1) (hb : d380014 q = 1) : d380132 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379698, d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379698, d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379699 q = 1) (hb : d380014 q = 1) : d380133 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379699, d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379699, d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379700 q = 1) (hb : d380014 q = 1) : d380134 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379700, d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379700, d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107875 (p : Pattern) (ha : d379706 p = 1) (hb : d380014 p = 1) : d380140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379701 q = 1) (hb : d380014 q = 1) : d380135 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379701, d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107874 q ha hb
    | true =>
      simp only [d379701, d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379702 q = 1) (hb : d380014 q = 1) : d380136 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379702, d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379702, d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379703 q = 1) (hb : d380014 q = 1) : d380137 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379703, d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379703, d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379704 q = 1) (hb : d380014 q = 1) : d380138 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379704, d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379704, d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379705 q = 1) (hb : d380014 q = 1) : d380139 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379705, d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379705, d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379706 q = 1) (hb : d380014 q = 1) : d380140 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379706, d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379706, d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107876 (p : Pattern) (ha : d379712 p = 1) (hb : d380014 p = 1) : d380146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379707 q = 1) (hb : d380014 q = 1) : d380141 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379707, d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107875 q ha hb
    | true =>
      simp only [d379707, d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379708 q = 1) (hb : d380014 q = 1) : d380142 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379708, d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379708, d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379709 q = 1) (hb : d380014 q = 1) : d380143 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379709, d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379709, d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379710 q = 1) (hb : d380014 q = 1) : d380144 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379710, d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379710, d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379711 q = 1) (hb : d380014 q = 1) : d380145 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379711, d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379711, d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379712 q = 1) (hb : d380014 q = 1) : d380146 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379712, d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379712, d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107877 (p : Pattern) (ha : d379718 p = 1) (hb : d380014 p = 1) : d380152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379713 q = 1) (hb : d380014 q = 1) : d380147 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379713, d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107876 q ha hb
    | true =>
      simp only [d379713, d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379714 q = 1) (hb : d380014 q = 1) : d380148 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379714, d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379714, d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379715 q = 1) (hb : d380014 q = 1) : d380149 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379715, d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379715, d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379716 q = 1) (hb : d380014 q = 1) : d380150 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379716, d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379716, d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379717 q = 1) (hb : d380014 q = 1) : d380151 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379717, d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379717, d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379718 q = 1) (hb : d380014 q = 1) : d380152 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379718, d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379718, d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107878 (p : Pattern) (ha : d379724 p = 1) (hb : d380014 p = 1) : d380158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379719 q = 1) (hb : d380014 q = 1) : d380153 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379719, d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107877 q ha hb
    | true =>
      simp only [d379719, d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379720 q = 1) (hb : d380014 q = 1) : d380154 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379720, d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379720, d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379721 q = 1) (hb : d380014 q = 1) : d380155 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379721, d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379721, d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379722 q = 1) (hb : d380014 q = 1) : d380156 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379722, d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379722, d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379723 q = 1) (hb : d380014 q = 1) : d380157 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379723, d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379723, d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379724 q = 1) (hb : d380014 q = 1) : d380158 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379724, d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379724, d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107879 (p : Pattern) (ha : d380020 p = 1) (hb : d380116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380015 q = 1) (hb : d380111 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380015, d380111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d380015, d380111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380016 q = 1) (hb : d380112 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380016, d380112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380016, d380112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380017 q = 1) (hb : d380113 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380017, d380113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380017, d380113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380018 q = 1) (hb : d380114 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380018, d380114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380018, d380114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380019 q = 1) (hb : d380115 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380019, d380115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380019, d380115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380020 q = 1) (hb : d380116 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380020, d380116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380020, d380116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107880 (p : Pattern) (ha : d380026 p = 1) (hb : d380122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380021 q = 1) (hb : d380117 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380021, d380117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107879 q ha hb
    | true =>
      simp only [d380021, d380117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380022 q = 1) (hb : d380118 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380022, d380118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380022, d380118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380023 q = 1) (hb : d380119 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380023, d380119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380023, d380119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380024 q = 1) (hb : d380120 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380024, d380120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380024, d380120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380025 q = 1) (hb : d380121 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380025, d380121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380025, d380121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380026 q = 1) (hb : d380122 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380026, d380122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380026, d380122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107881 (p : Pattern) (ha : d380032 p = 1) (hb : d380128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380027 q = 1) (hb : d380123 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380027, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107880 q ha hb
    | true =>
      simp only [d380027, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380028 q = 1) (hb : d380124 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380028, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380028, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380029 q = 1) (hb : d380125 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380029, d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380029, d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380030 q = 1) (hb : d380126 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380030, d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380030, d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380031 q = 1) (hb : d380127 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380031, d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380031, d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380032 q = 1) (hb : d380128 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380032, d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380032, d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107882 (p : Pattern) (ha : d380038 p = 1) (hb : d380134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380033 q = 1) (hb : d380129 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380033, d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107881 q ha hb
    | true =>
      simp only [d380033, d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380034 q = 1) (hb : d380130 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380034, d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380034, d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380035 q = 1) (hb : d380131 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380035, d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380035, d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380036 q = 1) (hb : d380132 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380036, d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380036, d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380037 q = 1) (hb : d380133 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380037, d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380037, d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380038 q = 1) (hb : d380134 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380038, d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380038, d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107883 (p : Pattern) (ha : d380044 p = 1) (hb : d380140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380039 q = 1) (hb : d380135 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380039, d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107882 q ha hb
    | true =>
      simp only [d380039, d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380040 q = 1) (hb : d380136 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380040, d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380040, d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380041 q = 1) (hb : d380137 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380041, d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380041, d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380042 q = 1) (hb : d380138 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380042, d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380042, d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380043 q = 1) (hb : d380139 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380043, d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380043, d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380044 q = 1) (hb : d380140 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380044, d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380044, d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107884 (p : Pattern) (ha : d380050 p = 1) (hb : d380146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380045 q = 1) (hb : d380141 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380045, d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107883 q ha hb
    | true =>
      simp only [d380045, d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380046 q = 1) (hb : d380142 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380046, d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380046, d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380047 q = 1) (hb : d380143 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380047, d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380047, d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380048 q = 1) (hb : d380144 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380048, d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380048, d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380049 q = 1) (hb : d380145 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380049, d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380049, d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380050 q = 1) (hb : d380146 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380050, d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380050, d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107885 (p : Pattern) (ha : d380056 p = 1) (hb : d380152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380051 q = 1) (hb : d380147 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380051, d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107884 q ha hb
    | true =>
      simp only [d380051, d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380052 q = 1) (hb : d380148 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380052, d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380052, d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380053 q = 1) (hb : d380149 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380053, d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380053, d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380054 q = 1) (hb : d380150 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380054, d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380054, d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380055 q = 1) (hb : d380151 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380055, d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380055, d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380056 q = 1) (hb : d380152 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380056, d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380056, d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107886 (p : Pattern) (ha : d380062 p = 1) (hb : d380158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380057 q = 1) (hb : d380153 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380057, d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107885 q ha hb
    | true =>
      simp only [d380057, d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380058 q = 1) (hb : d380154 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380058, d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380058, d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380059 q = 1) (hb : d380155 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380059, d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380059, d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380060 q = 1) (hb : d380156 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380060, d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380060, d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380061 q = 1) (hb : d380157 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380061, d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380061, d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380062 q = 1) (hb : d380158 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380062, d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380062, d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107887 (p : Pattern) (ha : d380068 p = 1) (hb : d380116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380063 q = 1) (hb : d380111 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380063, d380111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d380063, d380111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380064 q = 1) (hb : d380112 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380064, d380112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380064, d380112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380065 q = 1) (hb : d380113 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380065, d380113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380065, d380113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380066 q = 1) (hb : d380114 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380066, d380114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380066, d380114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380067 q = 1) (hb : d380115 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380067, d380115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380067, d380115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380068 q = 1) (hb : d380116 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380068, d380116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380068, d380116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107888 (p : Pattern) (ha : d380074 p = 1) (hb : d380122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380069 q = 1) (hb : d380117 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380069, d380117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107887 q ha hb
    | true =>
      simp only [d380069, d380117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380070 q = 1) (hb : d380118 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380070, d380118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380070, d380118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380071 q = 1) (hb : d380119 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380071, d380119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380071, d380119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380072 q = 1) (hb : d380120 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380072, d380120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380072, d380120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380073 q = 1) (hb : d380121 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380073, d380121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380073, d380121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380074 q = 1) (hb : d380122 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380074, d380122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380074, d380122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107889 (p : Pattern) (ha : d380080 p = 1) (hb : d380128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380075 q = 1) (hb : d380123 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380075, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107888 q ha hb
    | true =>
      simp only [d380075, d380123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380076 q = 1) (hb : d380124 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380076, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380076, d380124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380077 q = 1) (hb : d380125 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380077, d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380077, d380125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380078 q = 1) (hb : d380126 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380078, d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380078, d380126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380079 q = 1) (hb : d380127 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380079, d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380079, d380127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380080 q = 1) (hb : d380128 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380080, d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380080, d380128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107890 (p : Pattern) (ha : d380086 p = 1) (hb : d380134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380081 q = 1) (hb : d380129 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380081, d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107889 q ha hb
    | true =>
      simp only [d380081, d380129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380082 q = 1) (hb : d380130 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380082, d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380082, d380130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380083 q = 1) (hb : d380131 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380083, d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380083, d380131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380084 q = 1) (hb : d380132 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380084, d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380084, d380132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380085 q = 1) (hb : d380133 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380085, d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380085, d380133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380086 q = 1) (hb : d380134 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380086, d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380086, d380134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107891 (p : Pattern) (ha : d380092 p = 1) (hb : d380140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380087 q = 1) (hb : d380135 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380087, d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107890 q ha hb
    | true =>
      simp only [d380087, d380135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380088 q = 1) (hb : d380136 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380088, d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380088, d380136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380089 q = 1) (hb : d380137 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380089, d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380089, d380137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380090 q = 1) (hb : d380138 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380090, d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380090, d380138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380091 q = 1) (hb : d380139 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380091, d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380091, d380139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380092 q = 1) (hb : d380140 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380092, d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380092, d380140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107892 (p : Pattern) (ha : d380098 p = 1) (hb : d380146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380093 q = 1) (hb : d380141 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380093, d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107891 q ha hb
    | true =>
      simp only [d380093, d380141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380094 q = 1) (hb : d380142 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380094, d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380094, d380142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380095 q = 1) (hb : d380143 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380095, d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380095, d380143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380096 q = 1) (hb : d380144 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380096, d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380096, d380144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380097 q = 1) (hb : d380145 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380097, d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380097, d380145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380098 q = 1) (hb : d380146 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380098, d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380098, d380146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107893 (p : Pattern) (ha : d380104 p = 1) (hb : d380152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380099 q = 1) (hb : d380147 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380099, d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107892 q ha hb
    | true =>
      simp only [d380099, d380147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380100 q = 1) (hb : d380148 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380100, d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380100, d380148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380101 q = 1) (hb : d380149 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380101, d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380101, d380149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380102 q = 1) (hb : d380150 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380102, d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380102, d380150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380103 q = 1) (hb : d380151 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380103, d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380103, d380151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380104 q = 1) (hb : d380152 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380104, d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380104, d380152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107894 (p : Pattern) (ha : d380110 p = 1) (hb : d380158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380105 q = 1) (hb : d380153 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380105, d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107893 q ha hb
    | true =>
      simp only [d380105, d380153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380106 q = 1) (hb : d380154 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380106, d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380106, d380154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380107 q = 1) (hb : d380155 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380107, d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380107, d380155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380108 q = 1) (hb : d380156 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380108, d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380108, d380156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380109 q = 1) (hb : d380157 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380109, d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380109, d380157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380110 q = 1) (hb : d380158 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380110, d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380110, d380158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107895 (p : Pattern) (ha : d379641 p = 1) (hb : d380166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379640 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379641 q = 1) (hb : d380166 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379641, d380166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379641, d380166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro107896 (p : Pattern) (ha : d379647 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379642 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379642, d380167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107895 q ha hb
    | true =>
      simp only [d379642, d380167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379643 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379644 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d379645 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d379646 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d379647 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro107897 (p : Pattern) (ha : d379653 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379648 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107896 q ha hb
    | true =>
      simp only [d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379649 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379650 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379651 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379652 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379653 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107898 (p : Pattern) (ha : d379659 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379654 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107897 q ha hb
    | true =>
      simp only [d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379655 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379656 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379657 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379658 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379659 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107899 (p : Pattern) (ha : d379665 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379660 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107898 q ha hb
    | true =>
      simp only [d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379661 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379662 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379663 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379664 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379665 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107900 (p : Pattern) (ha : d379671 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379666 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107899 q ha hb
    | true =>
      simp only [d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379667 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379668 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379669 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379670 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379671 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107901 (p : Pattern) (ha : d379677 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379672 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107900 q ha hb
    | true =>
      simp only [d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379673 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379674 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379675 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379676 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379677 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107902 (p : Pattern) (ha : d0 p = 1) (hb : d380261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380261 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107903 (p : Pattern) (ha : d379688 p = 1) (hb : d380166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379688 q = 1) (hb : d380166 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379688, d380166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379688, d380166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro107904 (p : Pattern) (ha : d379694 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379689 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379689, d380167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107903 q ha hb
    | true =>
      simp only [d379689, d380167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379690 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379691 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d379692 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d379693 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d379694 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro107905 (p : Pattern) (ha : d379700 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379695 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107904 q ha hb
    | true =>
      simp only [d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379696 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379697 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379698 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379699 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379700 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107906 (p : Pattern) (ha : d379706 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379701 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107905 q ha hb
    | true =>
      simp only [d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379702 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379703 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379704 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379705 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379706 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107907 (p : Pattern) (ha : d379712 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379707 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107906 q ha hb
    | true =>
      simp only [d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379708 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379709 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379710 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379711 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379712 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107908 (p : Pattern) (ha : d379718 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379713 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107907 q ha hb
    | true =>
      simp only [d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379714 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379715 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379716 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379717 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379718 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107909 (p : Pattern) (ha : d379724 p = 1) (hb : d380167 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379719 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107908 q ha hb
    | true =>
      simp only [d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379720 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379721 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379722 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379723 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379724 q = 1) (hb : d380167 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107910 (p : Pattern) (ha : d0 p = 1) (hb : d380308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380308 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107911 (p : Pattern) (ha : d379641 p = 1) (hb : d380311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379640 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380310 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379641 q = 1) (hb : d380311 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379641, d380311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379641, d380311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro107912 (p : Pattern) (ha : d379647 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379642 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379642, d380312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107911 q ha hb
    | true =>
      simp only [d379642, d380312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379643 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379644 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d379645 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d379646 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d379647 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro107913 (p : Pattern) (ha : d379653 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379648 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107912 q ha hb
    | true =>
      simp only [d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379649 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379650 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379651 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379652 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379653 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107914 (p : Pattern) (ha : d379659 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379654 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107913 q ha hb
    | true =>
      simp only [d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379655 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379656 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379657 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379658 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379659 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107915 (p : Pattern) (ha : d379665 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379660 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107914 q ha hb
    | true =>
      simp only [d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379661 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379662 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379663 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379664 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379665 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107916 (p : Pattern) (ha : d379671 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379666 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107915 q ha hb
    | true =>
      simp only [d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379667 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379668 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379669 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379670 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379671 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107917 (p : Pattern) (ha : d379677 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379672 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107916 q ha hb
    | true =>
      simp only [d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379673 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379674 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379675 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379676 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379677 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107918 (p : Pattern) (ha : d379688 p = 1) (hb : d380311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380310 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379688 q = 1) (hb : d380311 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379688, d380311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379688, d380311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro107919 (p : Pattern) (ha : d379694 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379689 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379689, d380312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107918 q ha hb
    | true =>
      simp only [d379689, d380312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d379690 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d379691 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d379692 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d379693 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d379694 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro107920 (p : Pattern) (ha : d379700 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379695 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107919 q ha hb
    | true =>
      simp only [d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379696 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379697 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379698 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379699 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379700 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107921 (p : Pattern) (ha : d379706 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379701 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107920 q ha hb
    | true =>
      simp only [d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379702 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379703 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379704 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379705 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379706 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107922 (p : Pattern) (ha : d379712 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379707 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107921 q ha hb
    | true =>
      simp only [d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379708 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379709 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379710 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379711 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379712 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107923 (p : Pattern) (ha : d379718 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379713 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107922 q ha hb
    | true =>
      simp only [d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379714 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379715 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379716 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379717 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379718 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107924 (p : Pattern) (ha : d379724 p = 1) (hb : d380312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379719 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107923 q ha hb
    | true =>
      simp only [d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379720 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379721 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379722 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379723 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379724 q = 1) (hb : d380312 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107925 (p : Pattern) (ha : d379583 p = 1) (hb : d379677 p = 1) : d379677 p = 1 := by
  have h0 (q : Pattern) (ha : d379583 q = 1) (hb : d379677 q = 1) : d379677 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro107926 (p : Pattern) (ha : d379281 p = 1) (hb : d379635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d322122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105010 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319501 q = 1) (hb : d379631 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d379631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d379631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379278 q = 1) (hb : d379632 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379278, d379632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379278, d379632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d379279 q = 1) (hb : d379633 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379279, d379633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379279, d379633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d379280 q = 1) (hb : d379634 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379280, d379634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379280, d379634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d379281 q = 1) (hb : d379635 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379281, d379635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379281, d379635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h7 p ha hb
theorem andIntro107927 (p : Pattern) (ha : d379287 p = 1) (hb : d379641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379282 q = 1) (hb : d379636 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379282, d379636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107926 q ha hb
    | true =>
      simp only [d379282, d379636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379283 q = 1) (hb : d379637 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379283, d379637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379283, d379637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379284 q = 1) (hb : d379638 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379284, d379638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379284, d379638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379285 q = 1) (hb : d379639 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379285, d379639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379285, d379639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379286 q = 1) (hb : d379640 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379286, d379640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379286, d379640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379287 q = 1) (hb : d379641 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379287, d379641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379287, d379641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107928 (p : Pattern) (ha : d379293 p = 1) (hb : d379647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379288 q = 1) (hb : d379642 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379288, d379642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107927 q ha hb
    | true =>
      simp only [d379288, d379642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379289 q = 1) (hb : d379643 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379289, d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379289, d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379290 q = 1) (hb : d379644 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379290, d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379290, d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379291 q = 1) (hb : d379645 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379291, d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379291, d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379292 q = 1) (hb : d379646 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379292, d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379292, d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379293 q = 1) (hb : d379647 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379293, d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379293, d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107929 (p : Pattern) (ha : d379299 p = 1) (hb : d379653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379294 q = 1) (hb : d379648 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379294, d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107928 q ha hb
    | true =>
      simp only [d379294, d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379295 q = 1) (hb : d379649 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379295, d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379295, d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379296 q = 1) (hb : d379650 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379296, d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379296, d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379297 q = 1) (hb : d379651 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379297, d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379297, d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379298 q = 1) (hb : d379652 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379298, d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379298, d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379299 q = 1) (hb : d379653 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379299, d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379299, d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107930 (p : Pattern) (ha : d379305 p = 1) (hb : d379659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379300 q = 1) (hb : d379654 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379300, d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107929 q ha hb
    | true =>
      simp only [d379300, d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379301 q = 1) (hb : d379655 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379301, d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379301, d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379302 q = 1) (hb : d379656 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379302, d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379302, d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379303 q = 1) (hb : d379657 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379303, d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379303, d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379304 q = 1) (hb : d379658 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379304, d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379304, d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379305 q = 1) (hb : d379659 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379305, d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379305, d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107931 (p : Pattern) (ha : d379311 p = 1) (hb : d379665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379306 q = 1) (hb : d379660 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379306, d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107930 q ha hb
    | true =>
      simp only [d379306, d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379307 q = 1) (hb : d379661 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379307, d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379307, d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379308 q = 1) (hb : d379662 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379308, d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379308, d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379309 q = 1) (hb : d379663 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379309, d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379309, d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379310 q = 1) (hb : d379664 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379310, d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379310, d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379311 q = 1) (hb : d379665 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379311, d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379311, d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107932 (p : Pattern) (ha : d379317 p = 1) (hb : d379671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379312 q = 1) (hb : d379666 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379312, d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107931 q ha hb
    | true =>
      simp only [d379312, d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379313 q = 1) (hb : d379667 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379313, d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379313, d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379314 q = 1) (hb : d379668 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379314, d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379314, d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379315 q = 1) (hb : d379669 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379315, d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379315, d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379316 q = 1) (hb : d379670 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379316, d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379316, d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379317 q = 1) (hb : d379671 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379317, d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379317, d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107933 (p : Pattern) (ha : d379323 p = 1) (hb : d379677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379318 q = 1) (hb : d379672 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379318, d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107932 q ha hb
    | true =>
      simp only [d379318, d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379319 q = 1) (hb : d379673 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379319, d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379319, d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379320 q = 1) (hb : d379674 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379320, d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379320, d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379321 q = 1) (hb : d379675 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379321, d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379321, d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379322 q = 1) (hb : d379676 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379322, d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379322, d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379323 q = 1) (hb : d379677 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379323, d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379323, d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107934 (p : Pattern) (ha : d379583 p = 1) (hb : d379724 p = 1) : d379724 p = 1 := by
  have h0 (q : Pattern) (ha : d379583 q = 1) (hb : d379724 q = 1) : d379724 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro107935 (p : Pattern) (ha : d379281 p = 1) (hb : d379682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105144 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d319500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319501 q = 1) (hb : d379678 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d379678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d379678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379278 q = 1) (hb : d379679 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379278, d379679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379278, d379679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d379279 q = 1) (hb : d379680 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379279, d379680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379279, d379680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d379280 q = 1) (hb : d379681 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379280, d379681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379280, d379681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d379281 q = 1) (hb : d379682 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379281, d379682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379281, d379682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h7 p ha hb
theorem andIntro107936 (p : Pattern) (ha : d379287 p = 1) (hb : d379688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379282 q = 1) (hb : d379683 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379282, d379683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107935 q ha hb
    | true =>
      simp only [d379282, d379683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379283 q = 1) (hb : d379684 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379283, d379684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379283, d379684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379284 q = 1) (hb : d379685 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379284, d379685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379284, d379685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379285 q = 1) (hb : d379686 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379285, d379686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379285, d379686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379286 q = 1) (hb : d379687 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379286, d379687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379286, d379687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379287 q = 1) (hb : d379688 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379287, d379688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379287, d379688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107937 (p : Pattern) (ha : d379293 p = 1) (hb : d379694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379288 q = 1) (hb : d379689 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379288, d379689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107936 q ha hb
    | true =>
      simp only [d379288, d379689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379289 q = 1) (hb : d379690 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379289, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379289, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379290 q = 1) (hb : d379691 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379290, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379290, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379291 q = 1) (hb : d379692 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379291, d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379291, d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379292 q = 1) (hb : d379693 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379292, d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379292, d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379293 q = 1) (hb : d379694 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379293, d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379293, d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107938 (p : Pattern) (ha : d379299 p = 1) (hb : d379700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379294 q = 1) (hb : d379695 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379294, d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107937 q ha hb
    | true =>
      simp only [d379294, d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379295 q = 1) (hb : d379696 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379295, d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379295, d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379296 q = 1) (hb : d379697 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379296, d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379296, d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379297 q = 1) (hb : d379698 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379297, d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379297, d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379298 q = 1) (hb : d379699 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379298, d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379298, d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379299 q = 1) (hb : d379700 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379299, d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379299, d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107939 (p : Pattern) (ha : d379305 p = 1) (hb : d379706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379300 q = 1) (hb : d379701 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379300, d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107938 q ha hb
    | true =>
      simp only [d379300, d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379301 q = 1) (hb : d379702 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379301, d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379301, d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379302 q = 1) (hb : d379703 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379302, d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379302, d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379303 q = 1) (hb : d379704 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379303, d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379303, d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379304 q = 1) (hb : d379705 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379304, d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379304, d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379305 q = 1) (hb : d379706 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379305, d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379305, d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107940 (p : Pattern) (ha : d379311 p = 1) (hb : d379712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379306 q = 1) (hb : d379707 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379306, d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107939 q ha hb
    | true =>
      simp only [d379306, d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379307 q = 1) (hb : d379708 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379307, d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379307, d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379308 q = 1) (hb : d379709 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379308, d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379308, d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379309 q = 1) (hb : d379710 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379309, d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379309, d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379310 q = 1) (hb : d379711 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379310, d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379310, d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379311 q = 1) (hb : d379712 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379311, d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379311, d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107941 (p : Pattern) (ha : d379317 p = 1) (hb : d379718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379312 q = 1) (hb : d379713 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379312, d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107940 q ha hb
    | true =>
      simp only [d379312, d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379313 q = 1) (hb : d379714 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379313, d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379313, d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379314 q = 1) (hb : d379715 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379314, d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379314, d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379315 q = 1) (hb : d379716 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379315, d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379315, d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379316 q = 1) (hb : d379717 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379316, d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379316, d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379317 q = 1) (hb : d379718 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379317, d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379317, d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107942 (p : Pattern) (ha : d379323 p = 1) (hb : d379724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379318 q = 1) (hb : d379719 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379318, d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107941 q ha hb
    | true =>
      simp only [d379318, d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379319 q = 1) (hb : d379720 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379319, d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379319, d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379320 q = 1) (hb : d379721 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379320, d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379320, d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379321 q = 1) (hb : d379722 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379321, d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379321, d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379322 q = 1) (hb : d379723 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379322, d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379322, d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379323 q = 1) (hb : d379724 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379323, d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379323, d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107943 (p : Pattern) (ha : d379327 p = 1) (hb : d379682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d322122 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105176 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322163 q = 1) (hb : d379678 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322163, d379678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322163, d379678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379324 q = 1) (hb : d379679 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d379324, d379679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379324, d379679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d379325 q = 1) (hb : d379680 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d379325, d379680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379325, d379680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d379326 q = 1) (hb : d379681 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d379326, d379681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379326, d379681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d379327 q = 1) (hb : d379682 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d379327, d379682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379327, d379682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h7 p ha hb
theorem andIntro107944 (p : Pattern) (ha : d379333 p = 1) (hb : d379688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379328 q = 1) (hb : d379683 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d379328, d379683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107943 q ha hb
    | true =>
      simp only [d379328, d379683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379329 q = 1) (hb : d379684 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d379329, d379684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379329, d379684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379330 q = 1) (hb : d379685 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d379330, d379685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379330, d379685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379331 q = 1) (hb : d379686 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d379331, d379686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379331, d379686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379332 q = 1) (hb : d379687 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d379332, d379687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379332, d379687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379333 q = 1) (hb : d379688 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d379333, d379688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379333, d379688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107945 (p : Pattern) (ha : d379339 p = 1) (hb : d379694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379334 q = 1) (hb : d379689 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d379334, d379689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107944 q ha hb
    | true =>
      simp only [d379334, d379689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379335 q = 1) (hb : d379690 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379335, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379335, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379336 q = 1) (hb : d379691 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379336, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379336, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379337 q = 1) (hb : d379692 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379337, d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379337, d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379338 q = 1) (hb : d379693 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379338, d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379338, d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379339 q = 1) (hb : d379694 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379339, d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379339, d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107946 (p : Pattern) (ha : d379345 p = 1) (hb : d379700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379340 q = 1) (hb : d379695 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379340, d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107945 q ha hb
    | true =>
      simp only [d379340, d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379341 q = 1) (hb : d379696 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379341, d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379341, d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379342 q = 1) (hb : d379697 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379342, d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379342, d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379343 q = 1) (hb : d379698 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379343, d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379343, d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379344 q = 1) (hb : d379699 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379344, d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379344, d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379345 q = 1) (hb : d379700 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379345, d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379345, d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107947 (p : Pattern) (ha : d379351 p = 1) (hb : d379706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379346 q = 1) (hb : d379701 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379346, d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107946 q ha hb
    | true =>
      simp only [d379346, d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379347 q = 1) (hb : d379702 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379347, d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379347, d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379348 q = 1) (hb : d379703 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379348, d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379348, d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379349 q = 1) (hb : d379704 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379349, d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379349, d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379350 q = 1) (hb : d379705 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379350, d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379350, d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379351 q = 1) (hb : d379706 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379351, d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379351, d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107948 (p : Pattern) (ha : d379357 p = 1) (hb : d379712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379352 q = 1) (hb : d379707 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379352, d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107947 q ha hb
    | true =>
      simp only [d379352, d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379353 q = 1) (hb : d379708 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379353, d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379353, d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379354 q = 1) (hb : d379709 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379354, d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379354, d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379355 q = 1) (hb : d379710 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379355, d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379355, d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379356 q = 1) (hb : d379711 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379356, d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379356, d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379357 q = 1) (hb : d379712 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379357, d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379357, d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107949 (p : Pattern) (ha : d379363 p = 1) (hb : d379718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379358 q = 1) (hb : d379713 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379358, d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107948 q ha hb
    | true =>
      simp only [d379358, d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379359 q = 1) (hb : d379714 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379359, d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379359, d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379360 q = 1) (hb : d379715 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379360, d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379360, d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379361 q = 1) (hb : d379716 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379361, d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379361, d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379362 q = 1) (hb : d379717 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379362, d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379362, d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379363 q = 1) (hb : d379718 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379363, d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379363, d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107950 (p : Pattern) (ha : d379369 p = 1) (hb : d379724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379364 q = 1) (hb : d379719 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379364, d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107949 q ha hb
    | true =>
      simp only [d379364, d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379365 q = 1) (hb : d379720 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379365, d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379365, d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379366 q = 1) (hb : d379721 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379366, d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379366, d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379367 q = 1) (hb : d379722 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379367, d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379367, d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379368 q = 1) (hb : d379723 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379368, d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379368, d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379369 q = 1) (hb : d379724 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379369, d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379369, d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107951 (p : Pattern) (ha : d379647 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380317 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379643 q = 1) (hb : d380318 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379643, d380318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379643, d380318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379644 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379644, d380319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379644, d380319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379645 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379646 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379647 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro107952 (p : Pattern) (ha : d379653 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379648 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107951 q ha hb
    | true =>
      simp only [d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379649 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379650 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379651 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379652 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379653 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107953 (p : Pattern) (ha : d379659 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379654 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107952 q ha hb
    | true =>
      simp only [d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379655 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379656 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379657 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379658 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379659 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107954 (p : Pattern) (ha : d379665 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379660 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107953 q ha hb
    | true =>
      simp only [d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379661 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379662 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379663 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379664 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379665 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107955 (p : Pattern) (ha : d379671 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379666 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107954 q ha hb
    | true =>
      simp only [d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379667 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379668 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379669 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379670 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379671 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107956 (p : Pattern) (ha : d379677 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379672 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107955 q ha hb
    | true =>
      simp only [d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379673 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379674 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379675 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379676 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379677 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107957 (p : Pattern) (ha : d0 p = 1) (hb : d380405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380405 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107958 (p : Pattern) (ha : d379694 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379689 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d380317 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379690 q = 1) (hb : d380318 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379690, d380318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d379690, d380318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379691 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379691, d380319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379691, d380319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379692 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d379693 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d379694 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro107959 (p : Pattern) (ha : d379700 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379695 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107958 q ha hb
    | true =>
      simp only [d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379696 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379697 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379698 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379699 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379700 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107960 (p : Pattern) (ha : d379706 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379701 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107959 q ha hb
    | true =>
      simp only [d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379702 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379703 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379704 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379705 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379706 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107961 (p : Pattern) (ha : d379712 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379707 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107960 q ha hb
    | true =>
      simp only [d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379708 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379709 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379710 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379711 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379712 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107962 (p : Pattern) (ha : d379718 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379713 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107961 q ha hb
    | true =>
      simp only [d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379714 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379715 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379716 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379717 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379718 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107963 (p : Pattern) (ha : d379724 p = 1) (hb : d380319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379719 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107962 q ha hb
    | true =>
      simp only [d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d379720 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d379721 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d379722 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d379723 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d379724 q = 1) (hb : d380319 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107964 (p : Pattern) (ha : d0 p = 1) (hb : d380448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380448 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107965 (p : Pattern) (ha : d379563 p = 1) (hb : d379647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379562 q = 1) (hb : d379643 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379562, d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d379562, d379643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379644 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379563, d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379563, d379644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379645 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d379563 q = 1) (hb : d379646 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d379563 q = 1) (hb : d379647 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h8 p ha hb
theorem andIntro107966 (p : Pattern) (ha : d379563 p = 1) (hb : d379653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379563 q = 1) (hb : d379648 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107965 q ha hb
    | true =>
      simp only [d379648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379563 q = 1) (hb : d379649 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379563 q = 1) (hb : d379650 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379651 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379563 q = 1) (hb : d379652 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379653 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107967 (p : Pattern) (ha : d379563 p = 1) (hb : d379659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379563 q = 1) (hb : d379654 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107966 q ha hb
    | true =>
      simp only [d379654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379563 q = 1) (hb : d379655 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379563 q = 1) (hb : d379656 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379657 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379563 q = 1) (hb : d379658 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379659 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107968 (p : Pattern) (ha : d379563 p = 1) (hb : d379665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379563 q = 1) (hb : d379660 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107967 q ha hb
    | true =>
      simp only [d379660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379563 q = 1) (hb : d379661 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379563 q = 1) (hb : d379662 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379663 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379563 q = 1) (hb : d379664 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379665 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107969 (p : Pattern) (ha : d379563 p = 1) (hb : d379671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379563 q = 1) (hb : d379666 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107968 q ha hb
    | true =>
      simp only [d379666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379563 q = 1) (hb : d379667 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379563 q = 1) (hb : d379668 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379669 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379563 q = 1) (hb : d379670 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379671 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107970 (p : Pattern) (ha : d379563 p = 1) (hb : d379677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379563 q = 1) (hb : d379672 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107969 q ha hb
    | true =>
      simp only [d379672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379563 q = 1) (hb : d379673 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379563 q = 1) (hb : d379674 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379675 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379563 q = 1) (hb : d379676 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379677 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107971 (p : Pattern) (ha : d379563 p = 1) (hb : d379694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379689 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d379561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d379562 q = 1) (hb : d379690 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d379562, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d379562, d379690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379691 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d379563, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379563, d379691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379692 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d379563 q = 1) (hb : d379693 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d379693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h8 (q : Pattern) (ha : d379563 q = 1) (hb : d379694 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d379694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h8 p ha hb
theorem andIntro107972 (p : Pattern) (ha : d379563 p = 1) (hb : d379700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379563 q = 1) (hb : d379695 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107971 q ha hb
    | true =>
      simp only [d379695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379563 q = 1) (hb : d379696 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379563 q = 1) (hb : d379697 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379698 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379563 q = 1) (hb : d379699 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379700 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107973 (p : Pattern) (ha : d379563 p = 1) (hb : d379706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379563 q = 1) (hb : d379701 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107972 q ha hb
    | true =>
      simp only [d379701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379563 q = 1) (hb : d379702 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379563 q = 1) (hb : d379703 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379704 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379563 q = 1) (hb : d379705 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379706 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107974 (p : Pattern) (ha : d379563 p = 1) (hb : d379712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379563 q = 1) (hb : d379707 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107973 q ha hb
    | true =>
      simp only [d379707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379563 q = 1) (hb : d379708 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379563 q = 1) (hb : d379709 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379710 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379563 q = 1) (hb : d379711 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379712 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107975 (p : Pattern) (ha : d379563 p = 1) (hb : d379718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379563 q = 1) (hb : d379713 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107974 q ha hb
    | true =>
      simp only [d379713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379563 q = 1) (hb : d379714 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379563 q = 1) (hb : d379715 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379716 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379563 q = 1) (hb : d379717 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379718 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107976 (p : Pattern) (ha : d379563 p = 1) (hb : d379724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d379563 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d379563 q = 1) (hb : d379719 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107975 q ha hb
    | true =>
      simp only [d379719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d379563 q = 1) (hb : d379720 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d379720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d379563 q = 1) (hb : d379721 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d379721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d379563 q = 1) (hb : d379722 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d379722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d379563 q = 1) (hb : d379723 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d379723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d379563 q = 1) (hb : d379724 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d379724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107977 (p : Pattern) (ha : d322082 p = 1) (hb : d365770 p = 1) : d380504 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322043 q = 1) : d322043 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d322081 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322082 q = 1) (hb : d365770 q = 1) : d380504 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d322082, d365770, d380504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322082, d365770, d380504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro107978 (p : Pattern) (ha : d380068 p = 1) (hb : d380452 p = 1) : d380510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380063 q = 1) (hb : d380452 q = 1) : d380505 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380063, d380452, d380505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107977 q ha hb
    | true =>
      simp only [d380063, d380452, d380505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380452 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d380064 q = 1) (hb : d380452 q = 1) : d380506 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380064, d380506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380064, d380506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d380065 q = 1) (hb : d380452 q = 1) : d380507 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380065, d380507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380065, d380507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d380066 q = 1) (hb : d380452 q = 1) : d380508 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380066, d380508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380066, d380508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d380067 q = 1) (hb : d380452 q = 1) : d380509 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380067, d380509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380067, d380509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d380068 q = 1) (hb : d380452 q = 1) : d380510 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380068, d380510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380068, d380510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro107979 (p : Pattern) (ha : d380074 p = 1) (hb : d380454 p = 1) : d380516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380069 q = 1) (hb : d380452 q = 1) : d380511 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380069, d380511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107978 q ha hb
    | true =>
      simp only [d380069, d380511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380070 q = 1) (hb : d380452 q = 1) : d380512 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380070, d380512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380070, d380512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380071 q = 1) (hb : d380452 q = 1) : d380513 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380071, d380513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380071, d380513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380072 q = 1) (hb : d380452 q = 1) : d380514 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380072, d380514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380072, d380514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d380073 q = 1) (hb : d380453 q = 1) : d380515 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380073, d380453, d380515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380073, d380453, d380515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d380074 q = 1) (hb : d380454 q = 1) : d380516 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380074, d380454, d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380074, d380454, d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro107980 (p : Pattern) (ha : d380080 p = 1) (hb : d380454 p = 1) : d380522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380075 q = 1) (hb : d380454 q = 1) : d380517 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380075, d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107979 q ha hb
    | true =>
      simp only [d380075, d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380076 q = 1) (hb : d380454 q = 1) : d380518 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380076, d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380076, d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380077 q = 1) (hb : d380454 q = 1) : d380519 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380077, d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380077, d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380078 q = 1) (hb : d380454 q = 1) : d380520 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380078, d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380078, d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380079 q = 1) (hb : d380454 q = 1) : d380521 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380079, d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380079, d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380080 q = 1) (hb : d380454 q = 1) : d380522 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380080, d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380080, d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107981 (p : Pattern) (ha : d380086 p = 1) (hb : d380454 p = 1) : d380528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380081 q = 1) (hb : d380454 q = 1) : d380523 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380081, d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107980 q ha hb
    | true =>
      simp only [d380081, d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380082 q = 1) (hb : d380454 q = 1) : d380524 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380082, d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380082, d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380083 q = 1) (hb : d380454 q = 1) : d380525 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380083, d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380083, d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380084 q = 1) (hb : d380454 q = 1) : d380526 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380084, d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380084, d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380085 q = 1) (hb : d380454 q = 1) : d380527 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380085, d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380085, d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380086 q = 1) (hb : d380454 q = 1) : d380528 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380086, d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380086, d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107982 (p : Pattern) (ha : d380092 p = 1) (hb : d380454 p = 1) : d380534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380087 q = 1) (hb : d380454 q = 1) : d380529 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380087, d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107981 q ha hb
    | true =>
      simp only [d380087, d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380088 q = 1) (hb : d380454 q = 1) : d380530 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380088, d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380088, d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380089 q = 1) (hb : d380454 q = 1) : d380531 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380089, d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380089, d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380090 q = 1) (hb : d380454 q = 1) : d380532 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380090, d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380090, d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380091 q = 1) (hb : d380454 q = 1) : d380533 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380091, d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380091, d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380092 q = 1) (hb : d380454 q = 1) : d380534 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380092, d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380092, d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107983 (p : Pattern) (ha : d380098 p = 1) (hb : d380454 p = 1) : d380540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380093 q = 1) (hb : d380454 q = 1) : d380535 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380093, d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107982 q ha hb
    | true =>
      simp only [d380093, d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380094 q = 1) (hb : d380454 q = 1) : d380536 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380094, d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380094, d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380095 q = 1) (hb : d380454 q = 1) : d380537 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380095, d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380095, d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380096 q = 1) (hb : d380454 q = 1) : d380538 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380096, d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380096, d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380097 q = 1) (hb : d380454 q = 1) : d380539 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380097, d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380097, d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380098 q = 1) (hb : d380454 q = 1) : d380540 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380098, d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380098, d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107984 (p : Pattern) (ha : d380104 p = 1) (hb : d380454 p = 1) : d380546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380099 q = 1) (hb : d380454 q = 1) : d380541 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380099, d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107983 q ha hb
    | true =>
      simp only [d380099, d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380100 q = 1) (hb : d380454 q = 1) : d380542 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380100, d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380100, d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380101 q = 1) (hb : d380454 q = 1) : d380543 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380101, d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380101, d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380102 q = 1) (hb : d380454 q = 1) : d380544 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380102, d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380102, d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380103 q = 1) (hb : d380454 q = 1) : d380545 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380103, d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380103, d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380104 q = 1) (hb : d380454 q = 1) : d380546 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380104, d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380104, d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107985 (p : Pattern) (ha : d380110 p = 1) (hb : d380454 p = 1) : d380552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380105 q = 1) (hb : d380454 q = 1) : d380547 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380105, d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107984 q ha hb
    | true =>
      simp only [d380105, d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380106 q = 1) (hb : d380454 q = 1) : d380548 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380106, d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380106, d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380107 q = 1) (hb : d380454 q = 1) : d380549 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380107, d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380107, d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380108 q = 1) (hb : d380454 q = 1) : d380550 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380108, d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380108, d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380109 q = 1) (hb : d380454 q = 1) : d380551 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380109, d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380109, d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380110 q = 1) (hb : d380454 q = 1) : d380552 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380110, d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380110, d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107986 (p : Pattern) (ha : d380455 p = 1) (hb : d380504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d318809 q = 1) (hb : d322039 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d318809, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318809, d322039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104937 q ha hb
  have h6 (q : Pattern) (ha : d318810 q = 1) (hb : d322040 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d318810, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318810, d322040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d318811 q = 1) (hb : d322041 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d318811, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318811, d322041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d318812 q = 1) (hb : d322042 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d318812, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d318812, d322042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d318813 q = 1) (hb : d322043 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d318813, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d318813, d322043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d380455 q = 1) (hb : d380504 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d380455, d380504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d380455, d380504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro107987 (p : Pattern) (ha : d380461 p = 1) (hb : d380510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380456 q = 1) (hb : d380505 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380456, d380505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107986 q ha hb
    | true =>
      simp only [d380456, d380505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380457 q = 1) (hb : d380506 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380457, d380506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380457, d380506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380458 q = 1) (hb : d380507 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380458, d380507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380458, d380507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380459 q = 1) (hb : d380508 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380459, d380508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380459, d380508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380460 q = 1) (hb : d380509 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380460, d380509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380460, d380509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380461 q = 1) (hb : d380510 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380461, d380510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380461, d380510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107988 (p : Pattern) (ha : d380467 p = 1) (hb : d380516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380462 q = 1) (hb : d380511 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380462, d380511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107987 q ha hb
    | true =>
      simp only [d380462, d380511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380463 q = 1) (hb : d380512 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380463, d380512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380463, d380512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380464 q = 1) (hb : d380513 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380464, d380513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380464, d380513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380465 q = 1) (hb : d380514 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380465, d380514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380465, d380514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380466 q = 1) (hb : d380515 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380466, d380515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380466, d380515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380467 q = 1) (hb : d380516 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380467, d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380467, d380516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107989 (p : Pattern) (ha : d380473 p = 1) (hb : d380522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380468 q = 1) (hb : d380517 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380468, d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107988 q ha hb
    | true =>
      simp only [d380468, d380517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380469 q = 1) (hb : d380518 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380469, d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380469, d380518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380470 q = 1) (hb : d380519 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380470, d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380470, d380519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380471 q = 1) (hb : d380520 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380471, d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380471, d380520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380472 q = 1) (hb : d380521 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380472, d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380472, d380521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380473 q = 1) (hb : d380522 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380473, d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380473, d380522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107990 (p : Pattern) (ha : d380479 p = 1) (hb : d380528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380474 q = 1) (hb : d380523 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380474, d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107989 q ha hb
    | true =>
      simp only [d380474, d380523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380475 q = 1) (hb : d380524 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380475, d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380475, d380524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380476 q = 1) (hb : d380525 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380476, d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380476, d380525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380477 q = 1) (hb : d380526 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380477, d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380477, d380526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380478 q = 1) (hb : d380527 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380478, d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380478, d380527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380479 q = 1) (hb : d380528 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380479, d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380479, d380528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107991 (p : Pattern) (ha : d380485 p = 1) (hb : d380534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380480 q = 1) (hb : d380529 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d380480, d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107990 q ha hb
    | true =>
      simp only [d380480, d380529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380481 q = 1) (hb : d380530 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d380481, d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380481, d380530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380482 q = 1) (hb : d380531 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d380482, d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380482, d380531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380483 q = 1) (hb : d380532 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d380483, d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380483, d380532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380484 q = 1) (hb : d380533 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d380484, d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380484, d380533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380485 q = 1) (hb : d380534 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d380485, d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380485, d380534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107992 (p : Pattern) (ha : d380491 p = 1) (hb : d380540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380486 q = 1) (hb : d380535 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d380486, d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107991 q ha hb
    | true =>
      simp only [d380486, d380535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380487 q = 1) (hb : d380536 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d380487, d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380487, d380536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380488 q = 1) (hb : d380537 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d380488, d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380488, d380537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380489 q = 1) (hb : d380538 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d380489, d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380489, d380538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380490 q = 1) (hb : d380539 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d380490, d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380490, d380539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380491 q = 1) (hb : d380540 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d380491, d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380491, d380540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107993 (p : Pattern) (ha : d380497 p = 1) (hb : d380546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380492 q = 1) (hb : d380541 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d380492, d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107992 q ha hb
    | true =>
      simp only [d380492, d380541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380493 q = 1) (hb : d380542 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d380493, d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380493, d380542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380494 q = 1) (hb : d380543 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d380494, d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380494, d380543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380495 q = 1) (hb : d380544 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d380495, d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380495, d380544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380496 q = 1) (hb : d380545 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d380496, d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380496, d380545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380497 q = 1) (hb : d380546 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d380497, d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380497, d380546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107994 (p : Pattern) (ha : d380503 p = 1) (hb : d380552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380498 q = 1) (hb : d380547 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d380498, d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107993 q ha hb
    | true =>
      simp only [d380498, d380547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d380499 q = 1) (hb : d380548 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d380499, d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380499, d380548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d380500 q = 1) (hb : d380549 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d380500, d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380500, d380549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d380501 q = 1) (hb : d380550 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d380501, d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380501, d380550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d380502 q = 1) (hb : d380551 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d380502, d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380502, d380551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d380503 q = 1) (hb : d380552 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d380503, d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380503, d380552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107995 (p : Pattern) (ha : d365770 p = 1) (hb : d367625 p = 1) : d380553 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d53652 q = 1) : d53652 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d367624 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d365770 q = 1) (hb : d367625 q = 1) : d380553 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d365770, d367625, d380553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d365770, d367625, d380553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro107996 (p : Pattern) (ha : d380116 p = 1) (hb : d380452 p = 1) : d380559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380111 q = 1) (hb : d380452 q = 1) : d380554 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d380111, d380452, d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107995 q hb ha
    | true =>
      simp only [d380111, d380452, d380554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d380452 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d380112 q = 1) (hb : d380452 q = 1) : d380555 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d380112, d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380112, d380555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d380113 q = 1) (hb : d380452 q = 1) : d380556 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d380113, d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380113, d380556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d380114 q = 1) (hb : d380452 q = 1) : d380557 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d380114, d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380114, d380557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d380115 q = 1) (hb : d380452 q = 1) : d380558 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d380115, d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380115, d380558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d380116 q = 1) (hb : d380452 q = 1) : d380559 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d380116, d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380116, d380559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro107997 (p : Pattern) (ha : d380122 p = 1) (hb : d380454 p = 1) : d380565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380117 q = 1) (hb : d380452 q = 1) : d380560 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d380117, d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107996 q ha hb
    | true =>
      simp only [d380117, d380560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380118 q = 1) (hb : d380452 q = 1) : d380561 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d380118, d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380118, d380561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380119 q = 1) (hb : d380452 q = 1) : d380562 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d380119, d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380119, d380562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380120 q = 1) (hb : d380452 q = 1) : d380563 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d380120, d380563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380120, d380563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d380121 q = 1) (hb : d380453 q = 1) : d380564 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d380121, d380453, d380564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380121, d380453, d380564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d380122 q = 1) (hb : d380454 q = 1) : d380565 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d380122, d380454, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d380122, d380454, d380565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h7 p ha hb
theorem andIntro107998 (p : Pattern) (ha : d380128 p = 1) (hb : d380454 p = 1) : d380571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380123 q = 1) (hb : d380454 q = 1) : d380566 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d380123, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107997 q ha hb
    | true =>
      simp only [d380123, d380566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380124 q = 1) (hb : d380454 q = 1) : d380567 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d380124, d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380124, d380567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380125 q = 1) (hb : d380454 q = 1) : d380568 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d380125, d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380125, d380568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380126 q = 1) (hb : d380454 q = 1) : d380569 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d380126, d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380126, d380569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380127 q = 1) (hb : d380454 q = 1) : d380570 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d380127, d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380127, d380570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380128 q = 1) (hb : d380454 q = 1) : d380571 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d380128, d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380128, d380571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107999 (p : Pattern) (ha : d380134 p = 1) (hb : d380454 p = 1) : d380577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d380454 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d380129 q = 1) (hb : d380454 q = 1) : d380572 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d380129, d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107998 q ha hb
    | true =>
      simp only [d380129, d380572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d380130 q = 1) (hb : d380454 q = 1) : d380573 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d380130, d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d380130, d380573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d380131 q = 1) (hb : d380454 q = 1) : d380574 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d380131, d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d380131, d380574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d380132 q = 1) (hb : d380454 q = 1) : d380575 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d380132, d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d380132, d380575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d380133 q = 1) (hb : d380454 q = 1) : d380576 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d380133, d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d380133, d380576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d380134 q = 1) (hb : d380454 q = 1) : d380577 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d380134, d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d380134, d380577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
