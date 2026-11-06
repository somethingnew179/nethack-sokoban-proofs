import NetHack.Soko22Hazard87.AndIntroBlocks0247
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro62000 (p : Pattern) (ha : d148414 p = 1) (hb : d201642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148409 q = 1) (hb : d201632 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d148409, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148409, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61964 q ha hb
  have h2 (q : Pattern) (ha : d148217 q = 1) (hb : d201472 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d148217, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61964 q ha hb
    | true =>
      simp only [d148217, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148410 q = 1) (hb : d201633 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d148410, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148410, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148218 q = 1) (hb : d201473 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d148218, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148218, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148411 q = 1) (hb : d201634 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d148411, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148411, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148412 q = 1) (hb : d201635 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d148412, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148412, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148413 q = 1) (hb : d201641 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148413, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148413, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d148414 q = 1) (hb : d201642 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148414, d201642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148414, d201642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62001 (p : Pattern) (ha : d148420 p = 1) (hb : d201648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148391 q = 1) (hb : d201625 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148391, d201625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60461 q ha hb
    | true =>
      simp only [d148391, d201625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60462 q ha hb
  have h2 (q : Pattern) (ha : d148392 q = 1) (hb : d201626 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148392, d201626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148392, d201626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148393 q = 1) (hb : d201627 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148393, d201627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148393, d201627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148396 q = 1) (hb : d201628 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148396, d201628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60462 q ha hb
    | true =>
      simp only [d148396, d201628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52133 q hb ha
  have h5 (q : Pattern) (ha : d148397 q = 1) (hb : d201629 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148397, d201629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148397, d201629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148398 q = 1) (hb : d201630 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148398, d201630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148398, d201630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148399 q = 1) (hb : d201631 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148399, d201631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148399, d201631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148406 q = 1) (hb : d201638 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60462 q ha hb
    | true =>
      simp only [d148406, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
  have h9 (q : Pattern) (ha : d148407 q = 1) (hb : d201639 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148408 q = 1) (hb : d201640 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148415 q = 1) (hb : d201643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
    | true =>
      simp only [d148415, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62000 q ha hb
  have h12 (q : Pattern) (ha : d148416 q = 1) (hb : d201644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148417 q = 1) (hb : d201645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148418 q = 1) (hb : d201646 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148418, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148419 q = 1) (hb : d201647 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148419, d201647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148419, d201647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148420 q = 1) (hb : d201648 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148420, d201648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148420, d201648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro62002 (p : Pattern) (ha : d148425 p = 1) (hb : d201653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148406 q = 1) (hb : d201638 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60462 q ha hb
    | true =>
      simp only [d148406, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
  have h2 (q : Pattern) (ha : d148407 q = 1) (hb : d201639 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148408 q = 1) (hb : d201640 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148415 q = 1) (hb : d201643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
    | true =>
      simp only [d148415, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62000 q ha hb
  have h5 (q : Pattern) (ha : d148416 q = 1) (hb : d201644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148417 q = 1) (hb : d201645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148418 q = 1) (hb : d201646 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148418, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148423 q = 1) (hb : d201651 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148423, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148423, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148424 q = 1) (hb : d201652 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148424, d201652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148424, d201652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148425 q = 1) (hb : d201653 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148425, d201653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148425, d201653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro62003 (p : Pattern) (ha : d148431 p = 1) (hb : d201659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148421 q = 1) (hb : d201649 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148421, d201649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62001 q ha hb
    | true =>
      simp only [d148421, d201649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148422 q = 1) (hb : d201650 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148422, d201650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148422, d201650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148426 q = 1) (hb : d201654 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148426, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62002 q ha hb
    | true =>
      simp only [d148426, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148427 q = 1) (hb : d201655 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148427, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148427, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148428 q = 1) (hb : d201656 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148428, d201656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148428, d201656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148429 q = 1) (hb : d201657 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148429, d201657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148429, d201657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148430 q = 1) (hb : d201658 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148430, d201658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148430, d201658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148431 q = 1) (hb : d201659 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148431, d201659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148431, d201659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62004 (p : Pattern) (ha : d148433 p = 1) (hb : d201642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148400 q = 1) (hb : d201632 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d148400, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148400, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61962 q ha hb
  have h2 (q : Pattern) (ha : d148206 q = 1) (hb : d201472 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d148206, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61962 q ha hb
    | true =>
      simp only [d148206, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148401 q = 1) (hb : d201633 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d148401, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148401, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148207 q = 1) (hb : d201473 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d148207, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148207, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148402 q = 1) (hb : d201634 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d148402, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148402, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148403 q = 1) (hb : d201635 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d148403, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148403, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148432 q = 1) (hb : d201641 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148432, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148432, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d148433 q = 1) (hb : d201642 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148433, d201642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148433, d201642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62005 (p : Pattern) (ha : d148439 p = 1) (hb : d201661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148434 q = 1) (hb : d201643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148434, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
    | true =>
      simp only [d148434, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62004 q ha hb
  have h2 (q : Pattern) (ha : d148435 q = 1) (hb : d201644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148435, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148435, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148436 q = 1) (hb : d201645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148436, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148436, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148437 q = 1) (hb : d201651 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148437, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148437, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148438 q = 1) (hb : d201660 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148438, d201660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148438, d201660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148439 q = 1) (hb : d201661 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148439, d201661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148439, d201661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62006 (p : Pattern) (ha : d148445 p = 1) (hb : d201667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148426 q = 1) (hb : d201654 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148426, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62002 q ha hb
    | true =>
      simp only [d148426, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148427 q = 1) (hb : d201655 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148427, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148427, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148440 q = 1) (hb : d201662 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62005 q ha hb
    | true =>
      simp only [d148440, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148441 q = 1) (hb : d201663 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148442 q = 1) (hb : d201664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148442, d201664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148442, d201664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148443 q = 1) (hb : d201665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148443, d201665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148443, d201665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148444 q = 1) (hb : d201666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148444, d201666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148444, d201666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148445 q = 1) (hb : d201667 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148445, d201667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148445, d201667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62007 (p : Pattern) (ha : d148461 p = 1) (hb : d201670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148400 q = 1) (hb : d201632 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d148400, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148400, d201632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61962 q ha hb
  have h2 (q : Pattern) (ha : d148206 q = 1) (hb : d201472 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d148206, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61962 q ha hb
    | true =>
      simp only [d148206, d201472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148401 q = 1) (hb : d201633 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d148401, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148401, d201633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148207 q = 1) (hb : d201473 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d148207, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148207, d201473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148402 q = 1) (hb : d201634 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d148402, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148402, d201634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148403 q = 1) (hb : d201635 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d148403, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148403, d201635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148432 q = 1) (hb : d201641 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148432, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148432, d201641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148461 q = 1) (hb : d201670 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148461, d201670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148461, d201670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62008 (p : Pattern) (ha : d148467 p = 1) (hb : d201676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148406 q = 1) (hb : d201638 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60462 q ha hb
    | true =>
      simp only [d148406, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
  have h2 (q : Pattern) (ha : d148407 q = 1) (hb : d201639 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148408 q = 1) (hb : d201640 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148415 q = 1) (hb : d201643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
    | true =>
      simp only [d148415, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62000 q ha hb
  have h5 (q : Pattern) (ha : d148416 q = 1) (hb : d201644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148417 q = 1) (hb : d201645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148418 q = 1) (hb : d201646 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148418, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148462 q = 1) (hb : d201671 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148462, d201671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
    | true =>
      simp only [d148462, d201671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62007 q ha hb
  have h9 (q : Pattern) (ha : d148463 q = 1) (hb : d201672 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148463, d201672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148463, d201672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148464 q = 1) (hb : d201673 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148464, d201673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148464, d201673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148465 q = 1) (hb : d201674 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148465, d201674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148465, d201674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148466 q = 1) (hb : d201675 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148466, d201675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148466, d201675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148467 q = 1) (hb : d201676 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148467, d201676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148467, d201676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro62009 (p : Pattern) (ha : d148473 p = 1) (hb : d201682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148468 q = 1) (hb : d201677 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148468, d201677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62008 q ha hb
    | true =>
      simp only [d148468, d201677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148469 q = 1) (hb : d201678 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148469, d201678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148469, d201678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148470 q = 1) (hb : d201679 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148470, d201679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148470, d201679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148471 q = 1) (hb : d201680 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148471, d201680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148471, d201680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148472 q = 1) (hb : d201681 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148472, d201681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148472, d201681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148473 q = 1) (hb : d201682 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148473, d201682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148473, d201682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62010 (p : Pattern) (ha : d148479 p = 1) (hb : d201688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148446 q = 1) (hb : d201668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148446, d201668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62003 q ha hb
    | true =>
      simp only [d148446, d201668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62006 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148459 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148460 q = 1) (hb : d201669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148460, d201669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148460, d201669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148474 q = 1) (hb : d201683 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148474, d201683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62009 q ha hb
    | true =>
      simp only [d148474, d201683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148475 q = 1) (hb : d201684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148475, d201684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148475, d201684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148476 q = 1) (hb : d201685 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148476, d201685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148476, d201685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148477 q = 1) (hb : d201686 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148477, d201686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148477, d201686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148478 q = 1) (hb : d201687 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148478, d201687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148478, d201687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148479 q = 1) (hb : d201688 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148479, d201688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148479, d201688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62011 (p : Pattern) (ha : d148458 p = 1) (hb : d201693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148440 q = 1) (hb : d201662 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62005 q ha hb
    | true =>
      simp only [d148440, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148441 q = 1) (hb : d201663 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148455 q = 1) (hb : d201690 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148455, d201690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148455, d201690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148456 q = 1) (hb : d201691 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148456, d201691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148456, d201691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148457 q = 1) (hb : d201692 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148457, d201692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148457, d201692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148458 q = 1) (hb : d201693 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148458, d201693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148458, d201693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62012 (p : Pattern) (ha : d148486 p = 1) (hb : d201699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148481 q = 1) (hb : d201694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148481, d201694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62011 q ha hb
    | true =>
      simp only [d148481, d201694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148482 q = 1) (hb : d201695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148482, d201695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148482, d201695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148483 q = 1) (hb : d201696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148483, d201696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148483, d201696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148484 q = 1) (hb : d201697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148484, d201697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148484, d201697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148485 q = 1) (hb : d201698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148485, d201698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148485, d201698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148486 q = 1) (hb : d201699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148486, d201699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148486, d201699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62013 (p : Pattern) (ha : d148492 p = 1) (hb : d201705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148255 q = 1) (hb : d201510 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148255, d201510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148255, d201510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61971 q ha hb
  have h2 (q : Pattern) (ha : d148256 q = 1) (hb : d201511 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148256, d201511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148256, d201511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148265 q = 1) (hb : d201520 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148265, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61971 q ha hb
    | true =>
      simp only [d148265, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61974 q ha hb
  have h4 (q : Pattern) (ha : d148266 q = 1) (hb : d201521 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148266, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148266, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148267 q = 1) (hb : d201522 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148267, d201522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148267, d201522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148355 q = 1) (hb : d201597 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148355, d201597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61986 q ha hb
    | true =>
      simp only [d148355, d201597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61994 q ha hb
  have h7 (q : Pattern) (ha : d148373 q = 1) (hb : d201610 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148373, d201610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61995 q ha hb
    | true =>
      simp only [d148373, d201610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61996 q ha hb
  have h8 (q : Pattern) (ha : d148374 q = 1) (hb : d201611 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148374, d201611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148374, d201611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148375 q = 1) (hb : d201612 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148375, d201612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148375, d201612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d148376 q = 1) (hb : d201613 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148376, d201613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148376, d201613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148380 q = 1) (hb : d201617 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148380, d201617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148380, d201617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61997 q ha hb
  have h12 (q : Pattern) (ha : d148382 q = 1) (hb : d201619 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148382, d201619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148382, d201619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61998 q ha hb
  have h13 (q : Pattern) (ha : d148383 q = 1) (hb : d201620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148383, d201620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148383, d201620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148384 q = 1) (hb : d201621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148384, d201621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148384, d201621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148385 q = 1) (hb : d201622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148385, d201622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d148385, d201622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d148386 q = 1) (hb : d201623 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148386, d201623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148386, d201623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148480 q = 1) (hb : d201689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148480, d201689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148480, d201689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62010 q ha hb
  have h18 (q : Pattern) (ha : d148487 q = 1) (hb : d201700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148487, d201700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148487, d201700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62012 q ha hb
  have h19 (q : Pattern) (ha : d148488 q = 1) (hb : d201701 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148488, d201701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148488, d201701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148489 q = 1) (hb : d201702 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148489, d201702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148489, d201702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d148490 q = 1) (hb : d201703 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148490, d201703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d148490, d201703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d148491 q = 1) (hb : d201704 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148491, d201704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148491, d201704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148492 q = 1) (hb : d201705 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148492, d201705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148492, d201705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62014 (p : Pattern) (ha : d148498 p = 1) (hb : d201711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148493 q = 1) (hb : d201706 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148493, d201706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148493, d201706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62013 q ha hb
  have h2 (q : Pattern) (ha : d148494 q = 1) (hb : d201707 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148494, d201707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148494, d201707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148495 q = 1) (hb : d201708 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148495, d201708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148495, d201708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148496 q = 1) (hb : d201709 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148496, d201709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148496, d201709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148497 q = 1) (hb : d201710 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148497, d201710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148497, d201710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148498 q = 1) (hb : d201711 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148498, d201711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148498, d201711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62015 (p : Pattern) (ha : d148504 p = 1) (hb : d201717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d147261 q = 1) (hb : d200681 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147261, d200681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61746 q ha hb
    | true =>
      simp only [d147261, d200681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61787 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147500 q = 1) (hb : d200919 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147500, d200919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147500, d200919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61836 q ha hb
  have h3 (q : Pattern) (ha : d147501 q = 1) (hb : d200920 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147501, d200920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147501, d200920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147858 q = 1) (hb : d201202 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147858, d201202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147858, d201202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61899 q ha hb
  have h5 (q : Pattern) (ha : d147859 q = 1) (hb : d201203 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147859, d201203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147859, d201203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147860 q = 1) (hb : d201204 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d147860, d201204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147860, d201204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148199 q = 1) (hb : d201466 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148199, d201466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148199, d201466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61961 q ha hb
  have h8 (q : Pattern) (ha : d148200 q = 1) (hb : d201467 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148200, d201467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148200, d201467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148201 q = 1) (hb : d201468 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148201, d201468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148201, d201468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148202 q = 1) (hb : d201469 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148202, d201469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148202, d201469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148499 q = 1) (hb : d201712 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148499, d201712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148499, d201712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62014 q ha hb
  have h12 (q : Pattern) (ha : d148500 q = 1) (hb : d201713 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148500, d201713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148500, d201713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148501 q = 1) (hb : d201714 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148501, d201714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148501, d201714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148502 q = 1) (hb : d201715 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148502, d201715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148502, d201715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148503 q = 1) (hb : d201716 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d148503, d201716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148503, d201716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148504 q = 1) (hb : d201717 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d148504, d201717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148504, d201717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro62016 (p : Pattern) (ha : d148510 p = 1) (hb : d201723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148505 q = 1) (hb : d201718 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d148505, d201718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62015 q ha hb
    | true =>
      simp only [d148505, d201718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148506 q = 1) (hb : d201719 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d148506, d201719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148506, d201719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148507 q = 1) (hb : d201720 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d148507, d201720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148507, d201720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148508 q = 1) (hb : d201721 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d148508, d201721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148508, d201721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148509 q = 1) (hb : d201722 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d148509, d201722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148509, d201722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148510 q = 1) (hb : d201723 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d148510, d201723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148510, d201723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62017 (p : Pattern) (ha : d148516 p = 1) (hb : d201729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148511 q = 1) (hb : d201724 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d148511, d201724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62016 q ha hb
    | true =>
      simp only [d148511, d201724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148512 q = 1) (hb : d201725 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d148512, d201725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148512, d201725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148513 q = 1) (hb : d201726 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d148513, d201726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148513, d201726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148514 q = 1) (hb : d201727 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d148514, d201727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148514, d201727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148515 q = 1) (hb : d201728 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d148515, d201728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148515, d201728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148516 q = 1) (hb : d201729 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d148516, d201729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148516, d201729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62018 (p : Pattern) (ha : d148522 p = 1) (hb : d201735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148517 q = 1) (hb : d201730 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d148517, d201730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62017 q ha hb
    | true =>
      simp only [d148517, d201730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148518 q = 1) (hb : d201731 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d148518, d201731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148518, d201731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148519 q = 1) (hb : d201732 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d148519, d201732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148519, d201732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148520 q = 1) (hb : d201733 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d148520, d201733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148520, d201733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148521 q = 1) (hb : d201734 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d148521, d201734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148521, d201734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148522 q = 1) (hb : d201735 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d148522, d201735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148522, d201735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62019 (p : Pattern) (ha : d148528 p = 1) (hb : d201741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148523 q = 1) (hb : d201736 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d148523, d201736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62018 q ha hb
    | true =>
      simp only [d148523, d201736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148524 q = 1) (hb : d201737 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d148524, d201737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148524, d201737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148525 q = 1) (hb : d201738 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d148525, d201738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148525, d201738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148526 q = 1) (hb : d201739 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d148526, d201739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148526, d201739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148527 q = 1) (hb : d201740 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d148527, d201740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148527, d201740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148528 q = 1) (hb : d201741 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d148528, d201741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148528, d201741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62020 (p : Pattern) (ha : d148534 p = 1) (hb : d201747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148529 q = 1) (hb : d201742 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d148529, d201742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62019 q ha hb
    | true =>
      simp only [d148529, d201742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148530 q = 1) (hb : d201743 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d148530, d201743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148530, d201743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148531 q = 1) (hb : d201744 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d148531, d201744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148531, d201744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148532 q = 1) (hb : d201745 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d148532, d201745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148532, d201745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148533 q = 1) (hb : d201746 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d148533, d201746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148533, d201746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148534 q = 1) (hb : d201747 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d148534, d201747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148534, d201747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62021 (p : Pattern) (ha : d148540 p = 1) (hb : d201753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148535 q = 1) (hb : d201748 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d148535, d201748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62020 q ha hb
    | true =>
      simp only [d148535, d201748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148536 q = 1) (hb : d201749 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d148536, d201749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148536, d201749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148537 q = 1) (hb : d201750 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d148537, d201750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148537, d201750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148538 q = 1) (hb : d201751 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d148538, d201751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148538, d201751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148539 q = 1) (hb : d201752 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d148539, d201752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148539, d201752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148540 q = 1) (hb : d201753 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d148540, d201753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148540, d201753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62022 (p : Pattern) (ha : d148546 p = 1) (hb : d201759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148541 q = 1) (hb : d201754 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d148541, d201754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62021 q ha hb
    | true =>
      simp only [d148541, d201754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148542 q = 1) (hb : d201755 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d148542, d201755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148542, d201755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148543 q = 1) (hb : d201756 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d148543, d201756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148543, d201756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148544 q = 1) (hb : d201757 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d148544, d201757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148544, d201757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148545 q = 1) (hb : d201758 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d148545, d201758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148545, d201758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148546 q = 1) (hb : d201759 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d148546, d201759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148546, d201759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62023 (p : Pattern) (ha : d198467 p = 1) (hb : d245682 p = 1) : d201762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d198467 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25130 q = 1) (hb : d198467 q = 1) : d200271 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61393 q ha hb
    | true =>
      simp only [d25130, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25190 q = 1) (hb : d198467 q = 1) : d200327 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25191 q = 1) (hb : d198467 q = 1) : d200328 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25191, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25192 q = 1) (hb : d198467 q = 1) : d200329 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25193 q = 1) (hb : d198467 q = 1) : d200330 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d245682 q = 1) : d201762 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245682, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245682, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro62024 (p : Pattern) (ha : d198467 p = 1) (hb : d245692 p = 1) : d201772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d198467 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25166 q = 1) (hb : d198467 q = 1) : d200303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61398 q ha hb
    | true =>
      simp only [d25166, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245688 q = 1) : d201768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245688, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245688, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245689 q = 1) : d201769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245689, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245689, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245690 q = 1) : d201770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245690, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245690, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245691 q = 1) : d201771 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245691, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245691, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d245692 q = 1) : d201772 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245692, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245692, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62025 (p : Pattern) (ha : d198467 p = 1) (hb : d245698 p = 1) : d201778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25195 q = 1) (hb : d198467 q = 1) : d200332 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61401 q ha hb
    | true =>
      simp only [d25195, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61402 q ha hb
  have h2 (q : Pattern) (ha : d25196 q = 1) (hb : d198467 q = 1) : d200333 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25196, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245680 q = 1) : d201760 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245680, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245680, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245681 q = 1) : d201761 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245681, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245681, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245683 q = 1) : d201763 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245683, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245683, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62023 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245684 q = 1) : d201764 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245684, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245684, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d245685 q = 1) : d201765 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245685, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245685, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d245686 q = 1) : d201766 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245686, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245686, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d245687 q = 1) : d201767 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245687, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245687, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d245693 q = 1) : d201773 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245693, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245693, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62024 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d245694 q = 1) : d201774 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245694, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245694, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d245695 q = 1) : d201775 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245695, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245695, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d245696 q = 1) : d201776 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245696, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245696, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d245697 q = 1) : d201777 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245697, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245697, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d245698 q = 1) : d201778 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245698, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245698, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62026 (p : Pattern) (ha : d198467 p = 1) (hb : d245704 p = 1) : d201784 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d198467 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245699 q = 1) : d201779 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245699, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245699, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62025 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245700 q = 1) : d201780 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245700, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245700, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245701 q = 1) : d201781 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245701, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245701, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245702 q = 1) : d201782 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245702, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245702, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245703 q = 1) : d201783 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245703, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245703, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d245704 q = 1) : d201784 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245704, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245704, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62027 (p : Pattern) (ha : d198467 p = 1) (hb : d245707 p = 1) : d201787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25402 q = 1) (hb : d198467 q = 1) : d200491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61431 q ha hb
    | true =>
      simp only [d25402, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61432 q ha hb
  have h2 (q : Pattern) (ha : d25403 q = 1) (hb : d198467 q = 1) : d200492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25404 q = 1) (hb : d198467 q = 1) : d200493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25404, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25405 q = 1) (hb : d198467 q = 1) : d200494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25406 q = 1) (hb : d198467 q = 1) : d200495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245707 q = 1) : d201787 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245707, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245707, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62028 (p : Pattern) (ha : d198467 p = 1) (hb : d245718 p = 1) : d201798 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245713 q = 1) : d201793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245713, d201793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61466 q hb ha
    | true =>
      simp only [d245713, d201793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61438 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245714 q = 1) : d201794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245714, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245714, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245715 q = 1) : d201795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245715, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245715, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245716 q = 1) : d201796 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245716, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245716, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245717 q = 1) : d201797 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245717, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245717, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245718 q = 1) : d201798 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245718, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245718, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62029 (p : Pattern) (ha : d198467 p = 1) (hb : d245724 p = 1) : d201804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25408 q = 1) (hb : d198467 q = 1) : d200497 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25408, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61430 q ha hb
    | true =>
      simp only [d25408, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61433 q ha hb
  have h2 (q : Pattern) (ha : d25409 q = 1) (hb : d198467 q = 1) : d200498 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25409, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25409, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245705 q = 1) : d201785 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245705, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245705, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245706 q = 1) : d201786 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245706, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245706, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245708 q = 1) : d201788 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245708, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245708, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62027 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245709 q = 1) : d201789 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245709, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245709, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d245710 q = 1) : d201790 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245710, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245710, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d245711 q = 1) : d201791 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245711, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245711, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d245712 q = 1) : d201792 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245712, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245712, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d245719 q = 1) : d201799 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245719, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245719, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62028 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d245720 q = 1) : d201800 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245720, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245720, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d245721 q = 1) : d201801 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245721, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245721, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d245722 q = 1) : d201802 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245722, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245722, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d245723 q = 1) : d201803 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245723, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245723, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d245724 q = 1) : d201804 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245724, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245724, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62030 (p : Pattern) (ha : d198467 p = 1) (hb : d245730 p = 1) : d201810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245725 q = 1) : d201805 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245725, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245725, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62029 q ha hb
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245726 q = 1) : d201806 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245726, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245726, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245727 q = 1) : d201807 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245727, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245727, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245728 q = 1) : d201808 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245728, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245728, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245729 q = 1) : d201809 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245729, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245729, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245730 q = 1) : d201810 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245730, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245730, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62031 (p : Pattern) (ha : d198467 p = 1) (hb : d245734 p = 1) : d201814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25735 q = 1) (hb : d198467 q = 1) : d200719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25735, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61478 q ha hb
    | true =>
      simp only [d25735, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61479 q ha hb
  have h2 (q : Pattern) (ha : d25736 q = 1) (hb : d198467 q = 1) : d200720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25736, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25736, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25737 q = 1) (hb : d198467 q = 1) : d200721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25737, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25737, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25738 q = 1) (hb : d198467 q = 1) : d200722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25738, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25738, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25739 q = 1) (hb : d198467 q = 1) : d200723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25739, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25739, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245734 q = 1) : d201814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245734, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245734, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62032 (p : Pattern) (ha : d198467 p = 1) (hb : d245745 p = 1) : d201825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245740 q = 1) : d201820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245740, d201820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61515 q hb ha
    | true =>
      simp only [d245740, d201820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61486 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245741 q = 1) : d201821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245741, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245741, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245742 q = 1) : d201822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245742, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245742, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245743 q = 1) : d201823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245743, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245743, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245744 q = 1) : d201824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245744, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245744, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245745 q = 1) : d201825 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245745, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245745, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62033 (p : Pattern) (ha : d198467 p = 1) (hb : d245751 p = 1) : d201831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25741 q = 1) (hb : d198467 q = 1) : d200725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25741, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61477 q ha hb
    | true =>
      simp only [d25741, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61480 q ha hb
  have h2 (q : Pattern) (ha : d25742 q = 1) (hb : d198467 q = 1) : d200726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25742, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25742, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245732 q = 1) : d201812 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245732, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245732, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245733 q = 1) : d201813 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245733, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245733, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245735 q = 1) : d201815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245735, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245735, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62031 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245736 q = 1) : d201816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245736, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245736, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d245737 q = 1) : d201817 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245737, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245737, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d245738 q = 1) : d201818 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245738, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245738, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d245739 q = 1) : d201819 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245739, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245739, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d245746 q = 1) : d201826 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245746, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245746, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62032 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d245747 q = 1) : d201827 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245747, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245747, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d245748 q = 1) : d201828 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245748, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245748, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d245749 q = 1) : d201829 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245749, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245749, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d245750 q = 1) : d201830 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245750, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245750, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d245751 q = 1) : d201831 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245751, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245751, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62034 (p : Pattern) (ha : d198467 p = 1) (hb : d245757 p = 1) : d201837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245752 q = 1) : d201832 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245752, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245752, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62033 q ha hb
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245753 q = 1) : d201833 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245753, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245753, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245754 q = 1) : d201834 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245754, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245754, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245755 q = 1) : d201835 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245755, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245755, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245756 q = 1) : d201836 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245756, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245756, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245757 q = 1) : d201837 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245757, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245757, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62035 (p : Pattern) (ha : d198467 p = 1) (hb : d245762 p = 1) : d201842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26159 q = 1) (hb : d198467 q = 1) : d200977 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26159, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61533 q ha hb
    | true =>
      simp only [d26159, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61534 q ha hb
  have h2 (q : Pattern) (ha : d26160 q = 1) (hb : d198467 q = 1) : d200978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26160, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26160, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26161 q = 1) (hb : d198467 q = 1) : d200979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26161, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26161, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26162 q = 1) (hb : d198467 q = 1) : d200980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26162, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26162, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26163 q = 1) (hb : d198467 q = 1) : d200981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26163, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26163, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245762 q = 1) : d201842 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245762, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245762, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62036 (p : Pattern) (ha : d198467 p = 1) (hb : d245773 p = 1) : d201853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245768 q = 1) : d201848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245768, d201848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61573 q hb ha
    | true =>
      simp only [d245768, d201848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61542 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245769 q = 1) : d201849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245769, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245769, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245770 q = 1) : d201850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245770, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245770, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245771 q = 1) : d201851 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245771, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245771, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245772 q = 1) : d201852 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245772, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245772, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245773 q = 1) : d201853 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245773, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245773, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62037 (p : Pattern) (ha : d198467 p = 1) (hb : d245779 p = 1) : d201859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26165 q = 1) (hb : d198467 q = 1) : d200983 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26165, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61532 q ha hb
    | true =>
      simp only [d26165, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61535 q ha hb
  have h2 (q : Pattern) (ha : d26166 q = 1) (hb : d198467 q = 1) : d200984 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26166, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26166, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245760 q = 1) : d201840 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245760, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245760, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245761 q = 1) : d201841 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245761, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245761, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245763 q = 1) : d201843 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245763, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245763, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62035 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245764 q = 1) : d201844 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245764, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245764, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d245765 q = 1) : d201845 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245765, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245765, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d245766 q = 1) : d201846 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245766, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245766, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d245767 q = 1) : d201847 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245767, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245767, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d245774 q = 1) : d201854 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245774, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245774, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62036 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d245775 q = 1) : d201855 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245775, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245775, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d245776 q = 1) : d201856 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245776, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245776, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d245777 q = 1) : d201857 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245777, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245777, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d245778 q = 1) : d201858 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245778, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245778, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d245779 q = 1) : d201859 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245779, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245779, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62038 (p : Pattern) (ha : d198467 p = 1) (hb : d245785 p = 1) : d201865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245780 q = 1) : d201860 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245780, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245780, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62037 q ha hb
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245781 q = 1) : d201861 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245781, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245781, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245782 q = 1) : d201862 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245782, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245782, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245783 q = 1) : d201863 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245783, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245783, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245784 q = 1) : d201864 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245784, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245784, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245785 q = 1) : d201865 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245785, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245785, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62039 (p : Pattern) (ha : d198467 p = 1) (hb : d245791 p = 1) : d201871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26626 q = 1) (hb : d198467 q = 1) : d201256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26626, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61593 q ha hb
    | true =>
      simp only [d26626, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61594 q ha hb
  have h2 (q : Pattern) (ha : d26627 q = 1) (hb : d198467 q = 1) : d201257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26627, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26627, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26628 q = 1) (hb : d198467 q = 1) : d201258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26628, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26628, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26629 q = 1) (hb : d198467 q = 1) : d201259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26629, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26629, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26630 q = 1) (hb : d198467 q = 1) : d201260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26630, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26630, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245791 q = 1) : d201871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245791, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245791, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62040 (p : Pattern) (ha : d198467 p = 1) (hb : d245802 p = 1) : d201882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245797 q = 1) : d201877 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245797, d201877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61634 q hb ha
    | true =>
      simp only [d245797, d201877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61602 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245798 q = 1) : d201878 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245798, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245798, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245799 q = 1) : d201879 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245799, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245799, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245800 q = 1) : d201880 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245800, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245800, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245801 q = 1) : d201881 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245801, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245801, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245802 q = 1) : d201882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245802, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245802, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62041 (p : Pattern) (ha : d198467 p = 1) (hb : d245808 p = 1) : d201888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26632 q = 1) (hb : d198467 q = 1) : d201262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26632, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61592 q ha hb
    | true =>
      simp only [d26632, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61595 q ha hb
  have h2 (q : Pattern) (ha : d26633 q = 1) (hb : d198467 q = 1) : d201263 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26633, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26633, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245789 q = 1) : d201869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245789, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245789, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245790 q = 1) : d201870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245790, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245790, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245792 q = 1) : d201872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245792, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245792, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62039 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245793 q = 1) : d201873 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245793, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245793, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d245794 q = 1) : d201874 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245794, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245794, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d245795 q = 1) : d201875 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245795, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245795, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d245796 q = 1) : d201876 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245796, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245796, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d245803 q = 1) : d201883 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245803, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245803, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62040 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d245804 q = 1) : d201884 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245804, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245804, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d245805 q = 1) : d201885 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245805, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245805, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d245806 q = 1) : d201886 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245806, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245806, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d245807 q = 1) : d201887 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245807, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245807, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d245808 q = 1) : d201888 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245808, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245808, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62042 (p : Pattern) (ha : d198467 p = 1) (hb : d245814 p = 1) : d201894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245809 q = 1) : d201889 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245809, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245809, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62041 q ha hb
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245810 q = 1) : d201890 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245810, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245810, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245811 q = 1) : d201891 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245811, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245811, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245812 q = 1) : d201892 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245812, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245812, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245813 q = 1) : d201893 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245813, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245813, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245814 q = 1) : d201894 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245814, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245814, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62043 (p : Pattern) (ha : d198467 p = 1) (hb : d245821 p = 1) : d201901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27079 q = 1) (hb : d198467 q = 1) : d201514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27079, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61654 q ha hb
    | true =>
      simp only [d27079, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61655 q ha hb
  have h2 (q : Pattern) (ha : d27080 q = 1) (hb : d198467 q = 1) : d201515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27080, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27080, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27081 q = 1) (hb : d198467 q = 1) : d201516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27081, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27081, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27082 q = 1) (hb : d198467 q = 1) : d201517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27082, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27082, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27083 q = 1) (hb : d198467 q = 1) : d201518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27083, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27083, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245821 q = 1) : d201901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245821, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245821, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro62044 (p : Pattern) (ha : d198467 p = 1) (hb : d245832 p = 1) : d201912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245827 q = 1) : d201907 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d245827, d201907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61694 q hb ha
    | true =>
      simp only [d245827, d201907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61663 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245828 q = 1) : d201908 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245828, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245828, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245829 q = 1) : d201909 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245829, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245829, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245830 q = 1) : d201910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245830, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245830, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245831 q = 1) : d201911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245831, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245831, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245832 q = 1) : d201912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245832, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245832, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62045 (p : Pattern) (ha : d198467 p = 1) (hb : d245838 p = 1) : d201918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27085 q = 1) (hb : d198467 q = 1) : d201520 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27085, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61653 q ha hb
    | true =>
      simp only [d27085, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61656 q ha hb
  have h2 (q : Pattern) (ha : d27086 q = 1) (hb : d198467 q = 1) : d201521 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27086, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27086, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245819 q = 1) : d201899 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245819, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245819, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245820 q = 1) : d201900 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245820, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245820, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245822 q = 1) : d201902 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245822, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245822, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62043 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245823 q = 1) : d201903 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245823, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245823, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d245824 q = 1) : d201904 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245824, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245824, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d245825 q = 1) : d201905 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245825, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245825, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d245826 q = 1) : d201906 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245826, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245826, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d245833 q = 1) : d201913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245833, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245833, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62044 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d245834 q = 1) : d201914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245834, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245834, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d245835 q = 1) : d201915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245835, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245835, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d245836 q = 1) : d201916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245836, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245836, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d245837 q = 1) : d201917 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245837, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245837, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d245838 q = 1) : d201918 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245838, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245838, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62046 (p : Pattern) (ha : d198467 p = 1) (hb : d245844 p = 1) : d201924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245839 q = 1) : d201919 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245839, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245839, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62045 q ha hb
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245840 q = 1) : d201920 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245840, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245840, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245841 q = 1) : d201921 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245841, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245841, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245842 q = 1) : d201922 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245842, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245842, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245843 q = 1) : d201923 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245843, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245843, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245844 q = 1) : d201924 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245844, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245844, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62047 (p : Pattern) (ha : d198467 p = 1) (hb : d245850 p = 1) : d201930 p = 1 := by
  have h0 (q : Pattern) (ha : d198467 q = 1) (hb : d245731 q = 1) : d201811 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245731, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62026 q ha hb
    | true =>
      simp only [d245731, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62030 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245758 q = 1) : d201838 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245758, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245758, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62034 q ha hb
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245759 q = 1) : d201839 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245759, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245759, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245786 q = 1) : d201866 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245786, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245786, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62038 q ha hb
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245787 q = 1) : d201867 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245787, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245787, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245788 q = 1) : d201868 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245788, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245788, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d198467 q = 1) (hb : d245815 q = 1) : d201895 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245815, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245815, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62042 q ha hb
  have h8 (q : Pattern) (ha : d198467 q = 1) (hb : d245816 q = 1) : d201896 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245816, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245816, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d198467 q = 1) (hb : d245817 q = 1) : d201897 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245817, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245817, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198467 q = 1) (hb : d245818 q = 1) : d201898 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245818, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245818, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d198467 q = 1) (hb : d245845 q = 1) : d201925 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d245845, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245845, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62046 q ha hb
  have h12 (q : Pattern) (ha : d198467 q = 1) (hb : d245846 q = 1) : d201926 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d245846, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245846, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d198467 q = 1) (hb : d245847 q = 1) : d201927 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d245847, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245847, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d198467 q = 1) (hb : d245848 q = 1) : d201928 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d245848, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245848, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d198467 q = 1) (hb : d245849 q = 1) : d201929 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d245849, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245849, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d198467 q = 1) (hb : d245850 q = 1) : d201930 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d245850, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245850, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro62048 (p : Pattern) (ha : d198467 p = 1) (hb : d245856 p = 1) : d201936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245851 q = 1) : d201931 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d245851, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62047 q ha hb
    | true =>
      simp only [d245851, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245852 q = 1) : d201932 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d245852, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245852, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245853 q = 1) : d201933 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d245853, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245853, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245854 q = 1) : d201934 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d245854, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245854, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245855 q = 1) : d201935 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d245855, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245855, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245856 q = 1) : d201936 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d245856, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245856, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62049 (p : Pattern) (ha : d198467 p = 1) (hb : d245862 p = 1) : d201942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245857 q = 1) : d201937 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d245857, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62048 q ha hb
    | true =>
      simp only [d245857, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245858 q = 1) : d201938 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d245858, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245858, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245859 q = 1) : d201939 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d245859, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245859, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245860 q = 1) : d201940 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d245860, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245860, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245861 q = 1) : d201941 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d245861, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245861, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245862 q = 1) : d201942 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d245862, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245862, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62050 (p : Pattern) (ha : d198467 p = 1) (hb : d245868 p = 1) : d201948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245863 q = 1) : d201943 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d245863, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62049 q ha hb
    | true =>
      simp only [d245863, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245864 q = 1) : d201944 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d245864, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245864, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245865 q = 1) : d201945 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d245865, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245865, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245866 q = 1) : d201946 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d245866, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245866, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245867 q = 1) : d201947 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d245867, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245867, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245868 q = 1) : d201948 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d245868, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245868, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62051 (p : Pattern) (ha : d198467 p = 1) (hb : d245874 p = 1) : d201954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245869 q = 1) : d201949 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d245869, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62050 q ha hb
    | true =>
      simp only [d245869, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245870 q = 1) : d201950 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d245870, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245870, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245871 q = 1) : d201951 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d245871, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245871, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245872 q = 1) : d201952 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d245872, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245872, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245873 q = 1) : d201953 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d245873, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245873, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245874 q = 1) : d201954 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d245874, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245874, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62052 (p : Pattern) (ha : d198467 p = 1) (hb : d245880 p = 1) : d201960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245875 q = 1) : d201955 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d245875, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62051 q ha hb
    | true =>
      simp only [d245875, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245876 q = 1) : d201956 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d245876, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245876, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245877 q = 1) : d201957 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d245877, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245877, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245878 q = 1) : d201958 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d245878, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245878, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245879 q = 1) : d201959 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d245879, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245879, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245880 q = 1) : d201960 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d245880, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245880, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62053 (p : Pattern) (ha : d198467 p = 1) (hb : d245886 p = 1) : d201966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245881 q = 1) : d201961 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d245881, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62052 q ha hb
    | true =>
      simp only [d245881, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245882 q = 1) : d201962 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d245882, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245882, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245883 q = 1) : d201963 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d245883, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245883, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245884 q = 1) : d201964 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d245884, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245884, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245885 q = 1) : d201965 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d245885, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245885, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245886 q = 1) : d201966 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d245886, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245886, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62054 (p : Pattern) (ha : d198467 p = 1) (hb : d245892 p = 1) : d201972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d198467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d198467 q = 1) (hb : d245887 q = 1) : d201967 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d245887, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62053 q ha hb
    | true =>
      simp only [d245887, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d198467 q = 1) (hb : d245888 q = 1) : d201968 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d245888, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245888, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d198467 q = 1) (hb : d245889 q = 1) : d201969 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d245889, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245889, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d198467 q = 1) (hb : d245890 q = 1) : d201970 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d245890, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245890, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d198467 q = 1) (hb : d245891 q = 1) : d201971 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d245891, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245891, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d198467 q = 1) (hb : d245892 q = 1) : d201972 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d245892, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245892, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62055 (p : Pattern) (ha : d146966 p = 1) (hb : d200324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146928 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d146955 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d146852 q = 1) (hb : d200264 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61713 q ha hb
    | true =>
      simp only [d146852, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d146956 q = 1) (hb : d200320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d146956, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d146962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d146963 q = 1) (hb : d200321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146963, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d146964 q = 1) (hb : d200322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d146964, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146965 q = 1) (hb : d200323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146965, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146966 q = 1) (hb : d200324 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146966, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146966, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62056 (p : Pattern) (ha : d146985 p = 1) (hb : d200331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146928 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146955 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146852 q = 1) (hb : d200264 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61713 q ha hb
    | true =>
      simp only [d146852, d200264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d146956 q = 1) (hb : d200320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d146956, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d146962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d146963 q = 1) (hb : d200321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146963, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d146964 q = 1) (hb : d200322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146964, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146965 q = 1) (hb : d200323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146965, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d146971 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d146975 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d146977 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d146859 q = 1) (hb : d200271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61715 q ha hb
    | true =>
      simp only [d146859, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d146978 q = 1) (hb : d200327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d146978, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d146981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146982 q = 1) (hb : d200328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146982, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d146983 q = 1) (hb : d200329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146983, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d146983, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146984 q = 1) (hb : d200330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146984, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d146984, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146985 q = 1) (hb : d200331 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146985, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146985, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62057 (p : Pattern) (ha : d146994 p = 1) (hb : d201762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146977 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146859 q = 1) (hb : d200271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61715 q ha hb
    | true =>
      simp only [d146859, d200271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d146978 q = 1) (hb : d200327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146978, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146982 q = 1) (hb : d200328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146982, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146992 q = 1) (hb : d200329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146992, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146992, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146993 q = 1) (hb : d200330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146993, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146993, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146994 q = 1) (hb : d201762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146994, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146994, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62058 (p : Pattern) (ha : d147030 p = 1) (hb : d201772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147019 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146891 q = 1) (hb : d200303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146891, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61720 q ha hb
    | true =>
      simp only [d146891, d200303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d147020 q = 1) (hb : d201768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147020, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147020, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147027 q = 1) (hb : d201769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147027, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147027, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147028 q = 1) (hb : d201770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147028, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147028, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147029 q = 1) (hb : d201771 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147029, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147029, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147030 q = 1) (hb : d201772 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147030, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147030, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62059 (p : Pattern) (ha : d147036 p = 1) (hb : d201778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146922 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146986 q = 1) (hb : d200332 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146986, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62055 q ha hb
    | true =>
      simp only [d146986, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62056 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146989 q = 1) (hb : d200333 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146989, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146989, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146990 q = 1) (hb : d201760 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146990, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146990, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146991 q = 1) (hb : d201761 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146991, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146991, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146995 q = 1) (hb : d201763 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146995, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146995, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62057 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d146996 q = 1) (hb : d201764 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146996, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146996, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146997 q = 1) (hb : d201765 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146997, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146997, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d146998 q = 1) (hb : d201766 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146998, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146998, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d146999 q = 1) (hb : d201767 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146999, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146999, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147031 q = 1) (hb : d201773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147031, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147031, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62058 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147032 q = 1) (hb : d201774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147032, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147032, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147033 q = 1) (hb : d201775 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147033, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147033, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147034 q = 1) (hb : d201776 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147034, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147034, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147035 q = 1) (hb : d201777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147035, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147035, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147036 q = 1) (hb : d201778 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147036, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147036, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62060 (p : Pattern) (ha : d147042 p = 1) (hb : d201784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d146903 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d146903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d146903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28391 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d146904 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d146904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d146904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d146905 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d146905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d146905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d146906 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d146906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d146906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d146907 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d146907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d146907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147037 q = 1) (hb : d201779 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147037, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147037, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62059 q ha hb
  have h8 (q : Pattern) (ha : d147038 q = 1) (hb : d201780 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147038, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147038, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147039 q = 1) (hb : d201781 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147039, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147039, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147040 q = 1) (hb : d201782 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147040, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147040, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147041 q = 1) (hb : d201783 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147041, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147041, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d147042 q = 1) (hb : d201784 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147042, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147042, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro62061 (p : Pattern) (ha : d147136 p = 1) (hb : d200486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147060 q = 1) (hb : d200481 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61749 q ha hb
    | true =>
      simp only [d147060, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61750 q ha hb
  have h5 (q : Pattern) (ha : d147126 q = 1) (hb : d200482 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147126, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147132 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147133 q = 1) (hb : d200483 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147133, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147134 q = 1) (hb : d200484 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147134, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147135 q = 1) (hb : d200485 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147135, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147136 q = 1) (hb : d200486 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147136, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147136, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62062 (p : Pattern) (ha : d147157 p = 1) (hb : d200496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147060 q = 1) (hb : d200481 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61749 q ha hb
    | true =>
      simp only [d147060, d200481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61750 q ha hb
  have h4 (q : Pattern) (ha : d147126 q = 1) (hb : d200482 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147126, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147132 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147133 q = 1) (hb : d200483 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147133, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147134 q = 1) (hb : d200484 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147134, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147135 q = 1) (hb : d200485 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147135, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147142 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147147 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147149 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147070 q = 1) (hb : d200491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61752 q ha hb
    | true =>
      simp only [d147070, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61753 q ha hb
  have h13 (q : Pattern) (ha : d147150 q = 1) (hb : d200492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147150, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147154 q = 1) (hb : d200493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147154, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147155 q = 1) (hb : d200494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147155, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147155, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147156 q = 1) (hb : d200495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147156, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147156, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147157 q = 1) (hb : d200496 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147157, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147157, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62063 (p : Pattern) (ha : d147177 p = 1) (hb : d201787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147149 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147070 q = 1) (hb : d200491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61752 q ha hb
    | true =>
      simp only [d147070, d200491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61753 q ha hb
  have h3 (q : Pattern) (ha : d147150 q = 1) (hb : d200492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147150, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147154 q = 1) (hb : d200493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147154, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147175 q = 1) (hb : d200494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147175, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147175, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147176 q = 1) (hb : d200495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147176, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147176, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147177 q = 1) (hb : d201787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147177, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147177, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62064 (p : Pattern) (ha : d147241 p = 1) (hb : d201798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147230 q = 1) (hb : d201793 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147230, d201793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61781 q ha hb
    | true =>
      simp only [d147230, d201793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61784 q ha hb
  have h3 (q : Pattern) (ha : d147231 q = 1) (hb : d201794 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147231, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147231, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147237 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147238 q = 1) (hb : d201795 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147238, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147238, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147239 q = 1) (hb : d201796 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147239, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147239, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147240 q = 1) (hb : d201797 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147240, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147240, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147241 q = 1) (hb : d201798 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147241, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147241, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62065 (p : Pattern) (ha : d147254 p = 1) (hb : d201804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147078 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147158 q = 1) (hb : d200497 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147158, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62061 q ha hb
    | true =>
      simp only [d147158, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62062 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147172 q = 1) (hb : d200498 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147172, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147172, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147173 q = 1) (hb : d201785 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147173, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147173, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147174 q = 1) (hb : d201786 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147174, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147174, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147178 q = 1) (hb : d201788 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147178, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147178, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62063 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147180 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147181 q = 1) (hb : d201789 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147181, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147181, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147182 q = 1) (hb : d201790 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147182, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147182, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147183 q = 1) (hb : d201791 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147183, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147183, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147184 q = 1) (hb : d201792 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147184, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147184, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147242 q = 1) (hb : d201799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147242, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147242, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62064 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147249 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147250 q = 1) (hb : d201800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147250, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147250, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147251 q = 1) (hb : d201801 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147251, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147251, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147252 q = 1) (hb : d201802 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147252, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147252, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147253 q = 1) (hb : d201803 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147253, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147253, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147254 q = 1) (hb : d201804 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147254, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147254, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62066 (p : Pattern) (ha : d147260 p = 1) (hb : d201810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147255 q = 1) (hb : d201805 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147255, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147255, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62065 q ha hb
  have h2 (q : Pattern) (ha : d147256 q = 1) (hb : d201806 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147256, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147256, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147257 q = 1) (hb : d201807 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147257, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147257, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147258 q = 1) (hb : d201808 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147258, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147258, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147259 q = 1) (hb : d201809 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147259, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147259, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147260 q = 1) (hb : d201810 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147260, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147260, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62067 (p : Pattern) (ha : d147365 p = 1) (hb : d200714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147354 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147289 q = 1) (hb : d200709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61793 q ha hb
    | true =>
      simp only [d147289, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61794 q ha hb
  have h5 (q : Pattern) (ha : d147355 q = 1) (hb : d200710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147355, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147361 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147362 q = 1) (hb : d200711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147362, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147363 q = 1) (hb : d200712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147363, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147364 q = 1) (hb : d200713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147364, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147365 q = 1) (hb : d200714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147365, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147365, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62068 (p : Pattern) (ha : d147386 p = 1) (hb : d200724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147354 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147289 q = 1) (hb : d200709 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61793 q ha hb
    | true =>
      simp only [d147289, d200709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61794 q ha hb
  have h4 (q : Pattern) (ha : d147355 q = 1) (hb : d200710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147355, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147361 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147362 q = 1) (hb : d200711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147362, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147363 q = 1) (hb : d200712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147363, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147364 q = 1) (hb : d200713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147364, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147376 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147378 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147299 q = 1) (hb : d200719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61796 q ha hb
    | true =>
      simp only [d147299, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61797 q ha hb
  have h13 (q : Pattern) (ha : d147379 q = 1) (hb : d200720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147379, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147382 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147383 q = 1) (hb : d200721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147383, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147384 q = 1) (hb : d200722 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147384, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147384, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147385 q = 1) (hb : d200723 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147385, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147385, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147386 q = 1) (hb : d200724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147386, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147386, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62069 (p : Pattern) (ha : d147406 p = 1) (hb : d201814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147378 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147299 q = 1) (hb : d200719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61796 q ha hb
    | true =>
      simp only [d147299, d200719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61797 q ha hb
  have h3 (q : Pattern) (ha : d147379 q = 1) (hb : d200720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147379, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147382 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147383 q = 1) (hb : d200721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147383, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147404 q = 1) (hb : d200722 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147404, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147404, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147405 q = 1) (hb : d200723 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147405, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147405, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147406 q = 1) (hb : d201814 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147406, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147406, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62070 (p : Pattern) (ha : d147480 p = 1) (hb : d201825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147464 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147469 q = 1) (hb : d201820 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147469, d201820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61830 q ha hb
    | true =>
      simp only [d147469, d201820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61833 q ha hb
  have h3 (q : Pattern) (ha : d147470 q = 1) (hb : d201821 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147470, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147470, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147476 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147477 q = 1) (hb : d201822 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147477, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147477, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147478 q = 1) (hb : d201823 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147478, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147478, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147479 q = 1) (hb : d201824 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147479, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147479, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147480 q = 1) (hb : d201825 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147480, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147480, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62071 (p : Pattern) (ha : d147493 p = 1) (hb : d201831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147387 q = 1) (hb : d200725 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147387, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62067 q ha hb
    | true =>
      simp only [d147387, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62068 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147401 q = 1) (hb : d200726 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147401, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147401, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147402 q = 1) (hb : d201812 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147402, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147402, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147403 q = 1) (hb : d201813 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147403, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147403, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147407 q = 1) (hb : d201815 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147407, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147407, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62069 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147409 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147410 q = 1) (hb : d201816 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147410, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147410, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147411 q = 1) (hb : d201817 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147411, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147411, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147412 q = 1) (hb : d201818 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147412, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147412, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147413 q = 1) (hb : d201819 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147413, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147413, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147481 q = 1) (hb : d201826 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147481, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147481, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62070 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147488 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147489 q = 1) (hb : d201827 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147489, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147489, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147490 q = 1) (hb : d201828 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147490, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147490, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147491 q = 1) (hb : d201829 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147491, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147491, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147492 q = 1) (hb : d201830 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147492, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147492, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147493 q = 1) (hb : d201831 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147493, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147493, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62072 (p : Pattern) (ha : d147499 p = 1) (hb : d201837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147494 q = 1) (hb : d201832 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147494, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147494, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62071 q ha hb
  have h2 (q : Pattern) (ha : d147495 q = 1) (hb : d201833 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147495, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147495, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147496 q = 1) (hb : d201834 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147496, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147496, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147497 q = 1) (hb : d201835 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147497, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147497, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147498 q = 1) (hb : d201836 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147498, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147498, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147499 q = 1) (hb : d201837 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147499, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147499, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62073 (p : Pattern) (ha : d147664 p = 1) (hb : d200972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147599 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147644 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147564 q = 1) (hb : d200967 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61848 q ha hb
    | true =>
      simp only [d147564, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61849 q ha hb
  have h5 (q : Pattern) (ha : d147645 q = 1) (hb : d200968 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147645, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147660 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147661 q = 1) (hb : d200969 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147661, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147662 q = 1) (hb : d200970 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147662, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147663 q = 1) (hb : d200971 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147663, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147664 q = 1) (hb : d200972 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147664, d200972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147664, d200972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62074 (p : Pattern) (ha : d147686 p = 1) (hb : d200982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147590 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147644 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147564 q = 1) (hb : d200967 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61848 q ha hb
    | true =>
      simp only [d147564, d200967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61849 q ha hb
  have h4 (q : Pattern) (ha : d147645 q = 1) (hb : d200968 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147645, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147660 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147661 q = 1) (hb : d200969 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147661, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147662 q = 1) (hb : d200970 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147662, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147663 q = 1) (hb : d200971 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147663, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147670 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147675 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147678 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147574 q = 1) (hb : d200977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61851 q ha hb
    | true =>
      simp only [d147574, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61852 q ha hb
  have h13 (q : Pattern) (ha : d147679 q = 1) (hb : d200978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147679, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147682 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147683 q = 1) (hb : d200979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147683, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147684 q = 1) (hb : d200980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147684, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147684, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147685 q = 1) (hb : d200981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147685, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147685, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147686 q = 1) (hb : d200982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147686, d200982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147686, d200982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62075 (p : Pattern) (ha : d147711 p = 1) (hb : d201842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147574 q = 1) (hb : d200977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61851 q ha hb
    | true =>
      simp only [d147574, d200977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61852 q ha hb
  have h3 (q : Pattern) (ha : d147679 q = 1) (hb : d200978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147679, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147683 q = 1) (hb : d200979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147683, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147709 q = 1) (hb : d200980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147709, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147709, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147710 q = 1) (hb : d200981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147710, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147710, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147711 q = 1) (hb : d201842 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147711, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147711, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62076 (p : Pattern) (ha : d147807 p = 1) (hb : d201143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147765 q = 1) (hb : d201129 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61882 q ha hb
    | true =>
      simp only [d147765, d201129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61884 q ha hb
  have h2 (q : Pattern) (ha : d147766 q = 1) (hb : d201130 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d201130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147767 q = 1) (hb : d201131 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d201131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147774 q = 1) (hb : d201133 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61884 q ha hb
    | true =>
      simp only [d147774, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61885 q ha hb
  have h5 (q : Pattern) (ha : d147775 q = 1) (hb : d201134 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147776 q = 1) (hb : d201135 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147777 q = 1) (hb : d201136 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147777, d201136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147793 q = 1) (hb : d201133 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147793, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61884 q ha hb
    | true =>
      simp only [d147793, d201133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61889 q ha hb
  have h9 (q : Pattern) (ha : d147794 q = 1) (hb : d201134 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147794, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147794, d201134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147795 q = 1) (hb : d201135 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147795, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147795, d201135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147796 q = 1) (hb : d201141 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147796, d201141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147796, d201141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147806 q = 1) (hb : d201142 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147806, d201142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147806, d201142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147807 q = 1) (hb : d201143 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147807, d201143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147807, d201143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro62077 (p : Pattern) (ha : d147813 p = 1) (hb : d201157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147808 q = 1) (hb : d201144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147808, d201144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62076 q ha hb
    | true =>
      simp only [d147808, d201144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147809 q = 1) (hb : d201145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147809, d201145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147809, d201145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147799 q = 1) (hb : d201152 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147799, d201152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61890 q ha hb
    | true =>
      simp only [d147799, d201152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147800 q = 1) (hb : d201153 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147800, d201153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147800, d201153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147810 q = 1) (hb : d201154 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147810, d201154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147810, d201154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147811 q = 1) (hb : d201155 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147811, d201155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147811, d201155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147812 q = 1) (hb : d201156 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147812, d201156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147812, d201156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147813 q = 1) (hb : d201157 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147813, d201157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147813, d201157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62078 (p : Pattern) (ha : d147838 p = 1) (hb : d201853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147818 q = 1) (hb : d201848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147818, d201848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62077 q ha hb
    | true =>
      simp only [d147818, d201848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61896 q ha hb
  have h3 (q : Pattern) (ha : d147819 q = 1) (hb : d201849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147819, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147819, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147834 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147835 q = 1) (hb : d201850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147835, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147835, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147836 q = 1) (hb : d201851 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147836, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147836, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147837 q = 1) (hb : d201852 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147837, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147837, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147838 q = 1) (hb : d201853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147838, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147838, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62079 (p : Pattern) (ha : d147851 p = 1) (hb : d201859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147687 q = 1) (hb : d200983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147687, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62073 q ha hb
    | true =>
      simp only [d147687, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62074 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147706 q = 1) (hb : d200984 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147706, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147706, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147707 q = 1) (hb : d201840 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147707, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147707, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147708 q = 1) (hb : d201841 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147708, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147708, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147712 q = 1) (hb : d201843 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147712, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147712, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62075 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147714 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147715 q = 1) (hb : d201844 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147715, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147715, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147716 q = 1) (hb : d201845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147716, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147716, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147717 q = 1) (hb : d201846 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147717, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147717, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147718 q = 1) (hb : d201847 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147718, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147718, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147839 q = 1) (hb : d201854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147839, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147839, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62078 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147846 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147847 q = 1) (hb : d201855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147847, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147847, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147848 q = 1) (hb : d201856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147848, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147848, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147849 q = 1) (hb : d201857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147849, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147849, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147850 q = 1) (hb : d201858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147850, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147850, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147851 q = 1) (hb : d201859 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147851, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147851, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62080 (p : Pattern) (ha : d147857 p = 1) (hb : d201865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147852 q = 1) (hb : d201860 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147852, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147852, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62079 q ha hb
  have h2 (q : Pattern) (ha : d147853 q = 1) (hb : d201861 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147853, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147853, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147854 q = 1) (hb : d201862 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147854, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147854, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147855 q = 1) (hb : d201863 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147855, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147855, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147856 q = 1) (hb : d201864 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147856, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147856, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147857 q = 1) (hb : d201865 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147857, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147857, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62081 (p : Pattern) (ha : d148013 p = 1) (hb : d201251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147953 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147993 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147918 q = 1) (hb : d201246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61911 q ha hb
    | true =>
      simp only [d147918, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61912 q ha hb
  have h5 (q : Pattern) (ha : d147994 q = 1) (hb : d201247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147994, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d148009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148010 q = 1) (hb : d201248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148010, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148011 q = 1) (hb : d201249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148011, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148012 q = 1) (hb : d201250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148012, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148013 q = 1) (hb : d201251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148013, d201251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148013, d201251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62082 (p : Pattern) (ha : d148035 p = 1) (hb : d201261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147944 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147953 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147918 q = 1) (hb : d201246 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61911 q ha hb
    | true =>
      simp only [d147918, d201246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61912 q ha hb
  have h4 (q : Pattern) (ha : d147994 q = 1) (hb : d201247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147994, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148010 q = 1) (hb : d201248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148010, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148011 q = 1) (hb : d201249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148011, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148012 q = 1) (hb : d201250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148012, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148019 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148024 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d148027 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147928 q = 1) (hb : d201256 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61914 q ha hb
    | true =>
      simp only [d147928, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61915 q ha hb
  have h13 (q : Pattern) (ha : d148028 q = 1) (hb : d201257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d148028, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148031 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148032 q = 1) (hb : d201258 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148032, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148033 q = 1) (hb : d201259 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148033, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d148033, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148034 q = 1) (hb : d201260 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148034, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148034, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148035 q = 1) (hb : d201261 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148035, d201261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148035, d201261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62083 (p : Pattern) (ha : d148060 p = 1) (hb : d201871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147928 q = 1) (hb : d201256 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61914 q ha hb
    | true =>
      simp only [d147928, d201256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61915 q ha hb
  have h3 (q : Pattern) (ha : d148028 q = 1) (hb : d201257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148028, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148031 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148032 q = 1) (hb : d201258 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148032, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148058 q = 1) (hb : d201259 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148058, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148058, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148059 q = 1) (hb : d201260 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148059, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148059, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148060 q = 1) (hb : d201871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148060, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148060, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62084 (p : Pattern) (ha : d148148 p = 1) (hb : d201407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148106 q = 1) (hb : d201393 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61944 q ha hb
    | true =>
      simp only [d148106, d201393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61946 q ha hb
  have h2 (q : Pattern) (ha : d148107 q = 1) (hb : d201394 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d201394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148108 q = 1) (hb : d201395 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d201395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148115 q = 1) (hb : d201397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61946 q ha hb
    | true =>
      simp only [d148115, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61947 q ha hb
  have h5 (q : Pattern) (ha : d148116 q = 1) (hb : d201398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148117 q = 1) (hb : d201399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148118 q = 1) (hb : d201400 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148118, d201400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148134 q = 1) (hb : d201397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148134, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61946 q ha hb
    | true =>
      simp only [d148134, d201397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61951 q ha hb
  have h9 (q : Pattern) (ha : d148135 q = 1) (hb : d201398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148135, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148135, d201398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148136 q = 1) (hb : d201399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148136, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148136, d201399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148137 q = 1) (hb : d201405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148137, d201405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148137, d201405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148147 q = 1) (hb : d201406 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148147, d201406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148147, d201406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148148 q = 1) (hb : d201407 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148148, d201407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148148, d201407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro62085 (p : Pattern) (ha : d148154 p = 1) (hb : d201421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148149 q = 1) (hb : d201408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148149, d201408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62084 q ha hb
    | true =>
      simp only [d148149, d201408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148150 q = 1) (hb : d201409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148150, d201409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148150, d201409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148140 q = 1) (hb : d201416 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d201416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61952 q ha hb
    | true =>
      simp only [d148140, d201416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148141 q = 1) (hb : d201417 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d201417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d201417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148151 q = 1) (hb : d201418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148151, d201418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148151, d201418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148152 q = 1) (hb : d201419 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148152, d201419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148152, d201419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148153 q = 1) (hb : d201420 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148153, d201420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148153, d201420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148154 q = 1) (hb : d201421 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148154, d201421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148154, d201421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62086 (p : Pattern) (ha : d148179 p = 1) (hb : d201882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148159 q = 1) (hb : d201877 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148159, d201877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62085 q ha hb
    | true =>
      simp only [d148159, d201877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61958 q ha hb
  have h3 (q : Pattern) (ha : d148160 q = 1) (hb : d201878 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148160, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148160, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148175 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148176 q = 1) (hb : d201879 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148176, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148176, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148177 q = 1) (hb : d201880 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148177, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148177, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148178 q = 1) (hb : d201881 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148178, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148178, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148179 q = 1) (hb : d201882 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148179, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148179, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62087 (p : Pattern) (ha : d148192 p = 1) (hb : d201888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148036 q = 1) (hb : d201262 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148036, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62081 q ha hb
    | true =>
      simp only [d148036, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62082 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148055 q = 1) (hb : d201263 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148055, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148055, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148056 q = 1) (hb : d201869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148056, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148056, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148057 q = 1) (hb : d201870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148057, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148057, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148061 q = 1) (hb : d201872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148061, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148061, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62083 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d148063 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148064 q = 1) (hb : d201873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148064, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148064, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d148065 q = 1) (hb : d201874 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148065, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148065, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d148066 q = 1) (hb : d201875 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148066, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148066, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d148067 q = 1) (hb : d201876 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148067, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148067, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148180 q = 1) (hb : d201883 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148180, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148180, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62086 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148187 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148188 q = 1) (hb : d201884 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148188, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148188, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148189 q = 1) (hb : d201885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148189, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148189, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d148190 q = 1) (hb : d201886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148190, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148190, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d148191 q = 1) (hb : d201887 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148191, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148191, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d148192 q = 1) (hb : d201888 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148192, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148192, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62088 (p : Pattern) (ha : d148198 p = 1) (hb : d201894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148193 q = 1) (hb : d201889 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148193, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148193, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62087 q ha hb
  have h2 (q : Pattern) (ha : d148194 q = 1) (hb : d201890 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148194, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148194, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148195 q = 1) (hb : d201891 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148195, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148195, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148196 q = 1) (hb : d201892 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148196, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148196, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148197 q = 1) (hb : d201893 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148197, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148197, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148198 q = 1) (hb : d201894 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148198, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148198, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62089 (p : Pattern) (ha : d148332 p = 1) (hb : d201509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148275 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148312 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d148249 q = 1) (hb : d201504 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61969 q ha hb
    | true =>
      simp only [d148249, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61970 q ha hb
  have h5 (q : Pattern) (ha : d148313 q = 1) (hb : d201505 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d148313, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d148328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148329 q = 1) (hb : d201506 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148329, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148330 q = 1) (hb : d201507 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148330, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148331 q = 1) (hb : d201508 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148331, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148332 q = 1) (hb : d201509 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148332, d201509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148332, d201509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62090 (p : Pattern) (ha : d148354 p = 1) (hb : d201519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148249 q = 1) (hb : d201504 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61969 q ha hb
    | true =>
      simp only [d148249, d201504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61970 q ha hb
  have h4 (q : Pattern) (ha : d148313 q = 1) (hb : d201505 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148313, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148328 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148329 q = 1) (hb : d201506 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148329, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148330 q = 1) (hb : d201507 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148330, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148331 q = 1) (hb : d201508 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148331, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148338 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148343 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d148346 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d148259 q = 1) (hb : d201514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61972 q ha hb
    | true =>
      simp only [d148259, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61973 q ha hb
  have h13 (q : Pattern) (ha : d148347 q = 1) (hb : d201515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d148347, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148350 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148351 q = 1) (hb : d201516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148351, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148352 q = 1) (hb : d201517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148352, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d148352, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148353 q = 1) (hb : d201518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148353, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148353, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148354 q = 1) (hb : d201519 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148354, d201519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148354, d201519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62091 (p : Pattern) (ha : d148379 p = 1) (hb : d201901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148346 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148259 q = 1) (hb : d201514 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61972 q ha hb
    | true =>
      simp only [d148259, d201514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61973 q ha hb
  have h3 (q : Pattern) (ha : d148347 q = 1) (hb : d201515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148347, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148350 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148351 q = 1) (hb : d201516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148351, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148377 q = 1) (hb : d201517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148377, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148377, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148378 q = 1) (hb : d201518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148378, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148378, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148379 q = 1) (hb : d201901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148379, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148379, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62092 (p : Pattern) (ha : d148448 p = 1) (hb : d201653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148406 q = 1) (hb : d201638 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro60462 q ha hb
    | true =>
      simp only [d148406, d201638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
  have h2 (q : Pattern) (ha : d148407 q = 1) (hb : d201639 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d201639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148408 q = 1) (hb : d201640 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d201640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148415 q = 1) (hb : d201643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
    | true =>
      simp only [d148415, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62000 q ha hb
  have h5 (q : Pattern) (ha : d148416 q = 1) (hb : d201644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148417 q = 1) (hb : d201645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148418 q = 1) (hb : d201646 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148418, d201646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148434 q = 1) (hb : d201643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148434, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61999 q ha hb
    | true =>
      simp only [d148434, d201643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62004 q ha hb
  have h9 (q : Pattern) (ha : d148435 q = 1) (hb : d201644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148435, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148435, d201644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148436 q = 1) (hb : d201645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148436, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148436, d201645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148437 q = 1) (hb : d201651 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148437, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148437, d201651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148447 q = 1) (hb : d201652 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148447, d201652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148447, d201652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148448 q = 1) (hb : d201653 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148448, d201653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148448, d201653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro62093 (p : Pattern) (ha : d148454 p = 1) (hb : d201667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148449 q = 1) (hb : d201654 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148449, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62092 q ha hb
    | true =>
      simp only [d148449, d201654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148450 q = 1) (hb : d201655 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148450, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148450, d201655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148440 q = 1) (hb : d201662 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62005 q ha hb
    | true =>
      simp only [d148440, d201662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148441 q = 1) (hb : d201663 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d201663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148451 q = 1) (hb : d201664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148451, d201664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148451, d201664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148452 q = 1) (hb : d201665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148452, d201665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148452, d201665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148453 q = 1) (hb : d201666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148453, d201666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148453, d201666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148454 q = 1) (hb : d201667 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148454, d201667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148454, d201667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro62094 (p : Pattern) (ha : d148479 p = 1) (hb : d201912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148446 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148459 q = 1) (hb : d201907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148459, d201907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62093 q ha hb
    | true =>
      simp only [d148459, d201907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62011 q ha hb
  have h3 (q : Pattern) (ha : d148460 q = 1) (hb : d201908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148460, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148460, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148475 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148476 q = 1) (hb : d201909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148476, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148476, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148477 q = 1) (hb : d201910 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148477, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148477, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148478 q = 1) (hb : d201911 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148478, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148478, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148479 q = 1) (hb : d201912 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148479, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148479, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62095 (p : Pattern) (ha : d148492 p = 1) (hb : d201918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148267 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148355 q = 1) (hb : d201520 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148355, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62089 q ha hb
    | true =>
      simp only [d148355, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62090 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148373 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148374 q = 1) (hb : d201521 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148374, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148374, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148375 q = 1) (hb : d201899 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148375, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148375, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148376 q = 1) (hb : d201900 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148376, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148376, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148380 q = 1) (hb : d201902 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148380, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148380, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62091 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d148382 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148383 q = 1) (hb : d201903 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148383, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148383, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d148384 q = 1) (hb : d201904 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148384, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148384, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d148385 q = 1) (hb : d201905 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148385, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148385, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d148386 q = 1) (hb : d201906 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148386, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148386, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148480 q = 1) (hb : d201913 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148480, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148480, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62094 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148487 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148488 q = 1) (hb : d201914 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148488, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148488, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148489 q = 1) (hb : d201915 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148489, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148489, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d148490 q = 1) (hb : d201916 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148490, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148490, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d148491 q = 1) (hb : d201917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148491, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148491, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d148492 q = 1) (hb : d201918 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148492, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148492, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62096 (p : Pattern) (ha : d148498 p = 1) (hb : d201924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148493 q = 1) (hb : d201919 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148493, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148493, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62095 q ha hb
  have h2 (q : Pattern) (ha : d148494 q = 1) (hb : d201920 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148494, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148494, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148495 q = 1) (hb : d201921 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148495, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148495, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148496 q = 1) (hb : d201922 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148496, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148496, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148497 q = 1) (hb : d201923 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148497, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148497, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148498 q = 1) (hb : d201924 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148498, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148498, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62097 (p : Pattern) (ha : d148504 p = 1) (hb : d201930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d147261 q = 1) (hb : d201811 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147261, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62060 q ha hb
    | true =>
      simp only [d147261, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62066 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147500 q = 1) (hb : d201838 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147500, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147500, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62072 q ha hb
  have h3 (q : Pattern) (ha : d147501 q = 1) (hb : d201839 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147501, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147501, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147858 q = 1) (hb : d201866 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147858, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147858, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62080 q ha hb
  have h5 (q : Pattern) (ha : d147859 q = 1) (hb : d201867 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147859, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147859, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147860 q = 1) (hb : d201868 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d147860, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147860, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148199 q = 1) (hb : d201895 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148199, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148199, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62088 q ha hb
  have h8 (q : Pattern) (ha : d148200 q = 1) (hb : d201896 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148200, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148200, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148201 q = 1) (hb : d201897 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148201, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148201, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148202 q = 1) (hb : d201898 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148202, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148202, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148499 q = 1) (hb : d201925 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148499, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148499, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62096 q ha hb
  have h12 (q : Pattern) (ha : d148500 q = 1) (hb : d201926 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148500, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148500, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148501 q = 1) (hb : d201927 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148501, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148501, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148502 q = 1) (hb : d201928 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148502, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148502, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148503 q = 1) (hb : d201929 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d148503, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148503, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148504 q = 1) (hb : d201930 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d148504, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148504, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro62098 (p : Pattern) (ha : d148510 p = 1) (hb : d201936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148505 q = 1) (hb : d201931 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d148505, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62097 q ha hb
    | true =>
      simp only [d148505, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148506 q = 1) (hb : d201932 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d148506, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148506, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148507 q = 1) (hb : d201933 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d148507, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148507, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148508 q = 1) (hb : d201934 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d148508, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148508, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148509 q = 1) (hb : d201935 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d148509, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148509, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148510 q = 1) (hb : d201936 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d148510, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148510, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62099 (p : Pattern) (ha : d148516 p = 1) (hb : d201942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148511 q = 1) (hb : d201937 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d148511, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62098 q ha hb
    | true =>
      simp only [d148511, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148512 q = 1) (hb : d201938 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d148512, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148512, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148513 q = 1) (hb : d201939 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d148513, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148513, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148514 q = 1) (hb : d201940 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d148514, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148514, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148515 q = 1) (hb : d201941 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d148515, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148515, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148516 q = 1) (hb : d201942 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d148516, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148516, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62100 (p : Pattern) (ha : d148522 p = 1) (hb : d201948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148517 q = 1) (hb : d201943 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d148517, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62099 q ha hb
    | true =>
      simp only [d148517, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148518 q = 1) (hb : d201944 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d148518, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148518, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148519 q = 1) (hb : d201945 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d148519, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148519, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148520 q = 1) (hb : d201946 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d148520, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148520, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148521 q = 1) (hb : d201947 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d148521, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148521, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148522 q = 1) (hb : d201948 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d148522, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148522, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62101 (p : Pattern) (ha : d148528 p = 1) (hb : d201954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148523 q = 1) (hb : d201949 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d148523, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62100 q ha hb
    | true =>
      simp only [d148523, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148524 q = 1) (hb : d201950 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d148524, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148524, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148525 q = 1) (hb : d201951 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d148525, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148525, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148526 q = 1) (hb : d201952 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d148526, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148526, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148527 q = 1) (hb : d201953 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d148527, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148527, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148528 q = 1) (hb : d201954 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d148528, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148528, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62102 (p : Pattern) (ha : d148534 p = 1) (hb : d201960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148529 q = 1) (hb : d201955 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d148529, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62101 q ha hb
    | true =>
      simp only [d148529, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148530 q = 1) (hb : d201956 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d148530, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148530, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148531 q = 1) (hb : d201957 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d148531, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148531, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148532 q = 1) (hb : d201958 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d148532, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148532, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148533 q = 1) (hb : d201959 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d148533, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148533, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148534 q = 1) (hb : d201960 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d148534, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148534, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62103 (p : Pattern) (ha : d148540 p = 1) (hb : d201966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148535 q = 1) (hb : d201961 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d148535, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62102 q ha hb
    | true =>
      simp only [d148535, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148536 q = 1) (hb : d201962 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d148536, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148536, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148537 q = 1) (hb : d201963 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d148537, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148537, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148538 q = 1) (hb : d201964 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d148538, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148538, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148539 q = 1) (hb : d201965 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d148539, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148539, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148540 q = 1) (hb : d201966 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d148540, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148540, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62104 (p : Pattern) (ha : d148546 p = 1) (hb : d201972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148541 q = 1) (hb : d201967 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d148541, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62103 q ha hb
    | true =>
      simp only [d148541, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148542 q = 1) (hb : d201968 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d148542, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148542, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148543 q = 1) (hb : d201969 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d148543, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148543, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148544 q = 1) (hb : d201970 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d148544, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148544, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148545 q = 1) (hb : d201971 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d148545, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148545, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148546 q = 1) (hb : d201972 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d148546, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148546, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro62105 (p : Pattern) (ha : d150039 p = 1) (hb : d200324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20982 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21009 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200264 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150035 q = 1) (hb : d200320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150035, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21031 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150036 q = 1) (hb : d200321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150036, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150037 q = 1) (hb : d200322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150037, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150038 q = 1) (hb : d200323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150038, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150039 q = 1) (hb : d200324 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150039, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150039, d200324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62106 (p : Pattern) (ha : d150044 p = 1) (hb : d200331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20982 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20988 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21009 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d200264 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150035 q = 1) (hb : d200320 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150035, d200320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21031 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150036 q = 1) (hb : d200321 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150036, d200321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150037 q = 1) (hb : d200322 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150037, d200322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150038 q = 1) (hb : d200323 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150038, d200323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21040 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21044 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21046 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d200271 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150040 q = 1) (hb : d200327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150040, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21052 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150041 q = 1) (hb : d200328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150041, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150042 q = 1) (hb : d200329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150042, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150042, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150043 q = 1) (hb : d200330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150043, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150043, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150044 q = 1) (hb : d200331 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150044, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150044, d200331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62107 (p : Pattern) (ha : d150051 p = 1) (hb : d201762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21046 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200271 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150040 q = 1) (hb : d200327 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150040, d200327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21052 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150041 q = 1) (hb : d200328 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150041, d200328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150049 q = 1) (hb : d200329 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150049, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150049, d200329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150050 q = 1) (hb : d200330 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150050, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150050, d200330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150051 q = 1) (hb : d201762 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150051, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150051, d201762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62108 (p : Pattern) (ha : d150061 p = 1) (hb : d201772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21090 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200303 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150057 q = 1) (hb : d201768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150057, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150057, d201768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21112 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150058 q = 1) (hb : d201769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150058, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150058, d201769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150059 q = 1) (hb : d201770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150059, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150059, d201770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150060 q = 1) (hb : d201771 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150060, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150060, d201771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150061 q = 1) (hb : d201772 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150061, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150061, d201772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62109 (p : Pattern) (ha : d150067 p = 1) (hb : d201778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20976 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150045 q = 1) (hb : d200332 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150045, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62105 q ha hb
    | true =>
      simp only [d150045, d200332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62106 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21059 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150046 q = 1) (hb : d200333 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150046, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150046, d200333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150047 q = 1) (hb : d201760 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150047, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150047, d201760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150048 q = 1) (hb : d201761 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150048, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150048, d201761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150052 q = 1) (hb : d201763 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150052, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150052, d201763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62107 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150053 q = 1) (hb : d201764 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150053, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150053, d201764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150054 q = 1) (hb : d201765 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150054, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150054, d201765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150055 q = 1) (hb : d201766 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150055, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150055, d201766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150056 q = 1) (hb : d201767 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150056, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150056, d201767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150062 q = 1) (hb : d201773 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150062, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150062, d201773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62108 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150063 q = 1) (hb : d201774 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150063, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150063, d201774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150064 q = 1) (hb : d201775 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150064, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150064, d201775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150065 q = 1) (hb : d201776 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150065, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150065, d201776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150066 q = 1) (hb : d201777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150066, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150066, d201777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150067 q = 1) (hb : d201778 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150067, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150067, d201778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62110 (p : Pattern) (ha : d150073 p = 1) (hb : d201784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d150030 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d150030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d150030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28446 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d150031 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d150031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d150031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d150032 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d150032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d150032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d150033 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d150033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d150033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d150034 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d150034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d150034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150068 q = 1) (hb : d201779 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150068, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150068, d201779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62109 q ha hb
  have h8 (q : Pattern) (ha : d150069 q = 1) (hb : d201780 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150069, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150069, d201780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150070 q = 1) (hb : d201781 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150070, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150070, d201781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150071 q = 1) (hb : d201782 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150071, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150071, d201782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150072 q = 1) (hb : d201783 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150072, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150072, d201783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150073 q = 1) (hb : d201784 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150073, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d150073, d201784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro62111 (p : Pattern) (ha : d150078 p = 1) (hb : d200486 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21172 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21181 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21211 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200481 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150074 q = 1) (hb : d200482 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150074, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21253 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150075 q = 1) (hb : d200483 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150075, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150076 q = 1) (hb : d200484 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150076, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150077 q = 1) (hb : d200485 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150077, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150078 q = 1) (hb : d200486 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150078, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150078, d200486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62112 (p : Pattern) (ha : d150083 p = 1) (hb : d200496 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21172 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21181 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21211 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d200481 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150074 q = 1) (hb : d200482 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150074, d200482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21253 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150075 q = 1) (hb : d200483 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150075, d200483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150076 q = 1) (hb : d200484 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150076, d200484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150077 q = 1) (hb : d200485 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150077, d200485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21263 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21268 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21270 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d200491 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150079 q = 1) (hb : d200492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150079, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21277 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150080 q = 1) (hb : d200493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150080, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150081 q = 1) (hb : d200494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150081, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150081, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150082 q = 1) (hb : d200495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150082, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150082, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150083 q = 1) (hb : d200496 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150083, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150083, d200496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62113 (p : Pattern) (ha : d150090 p = 1) (hb : d201787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21270 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200491 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150079 q = 1) (hb : d200492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150079, d200492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21277 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150080 q = 1) (hb : d200493 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150080, d200493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150088 q = 1) (hb : d200494 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150088, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150088, d200494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150089 q = 1) (hb : d200495 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150089, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150089, d200495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150090 q = 1) (hb : d201787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150090, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150090, d201787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62114 (p : Pattern) (ha : d150100 p = 1) (hb : d201798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150096 q = 1) (hb : d201794 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150096, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150096, d201794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21389 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150097 q = 1) (hb : d201795 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150097, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150097, d201795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150098 q = 1) (hb : d201796 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150098, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150098, d201796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150099 q = 1) (hb : d201797 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150099, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150099, d201797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150100 q = 1) (hb : d201798 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150100, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150100, d201798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62115 (p : Pattern) (ha : d150106 p = 1) (hb : d201804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21164 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150084 q = 1) (hb : d200497 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150084, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62111 q ha hb
    | true =>
      simp only [d150084, d200497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62112 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21295 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150085 q = 1) (hb : d200498 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150085, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150085, d200498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150086 q = 1) (hb : d201785 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150086, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150086, d201785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150087 q = 1) (hb : d201786 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150087, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150087, d201786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150091 q = 1) (hb : d201788 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150091, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150091, d201788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62113 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d21304 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150092 q = 1) (hb : d201789 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150092, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150092, d201789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150093 q = 1) (hb : d201790 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150093, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150093, d201790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150094 q = 1) (hb : d201791 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150094, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150094, d201791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150095 q = 1) (hb : d201792 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150095, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150095, d201792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150101 q = 1) (hb : d201799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150101, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150101, d201799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62114 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21405 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150102 q = 1) (hb : d201800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150102, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150102, d201800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150103 q = 1) (hb : d201801 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150103, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150103, d201801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150104 q = 1) (hb : d201802 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150104, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150104, d201802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150105 q = 1) (hb : d201803 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150105, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150105, d201803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150106 q = 1) (hb : d201804 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150106, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150106, d201804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62116 (p : Pattern) (ha : d150112 p = 1) (hb : d201810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150107 q = 1) (hb : d201805 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150107, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150107, d201805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62115 q ha hb
  have h2 (q : Pattern) (ha : d150108 q = 1) (hb : d201806 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150108, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150108, d201806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150109 q = 1) (hb : d201807 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150109, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150109, d201807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150110 q = 1) (hb : d201808 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150110, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150110, d201808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150111 q = 1) (hb : d201809 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150111, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150111, d201809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150112 q = 1) (hb : d201810 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150112, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150112, d201810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62117 (p : Pattern) (ha : d150118 p = 1) (hb : d200714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21471 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21480 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21510 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200709 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150114 q = 1) (hb : d200710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150114, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21556 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150115 q = 1) (hb : d200711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150115, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150116 q = 1) (hb : d200712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150116, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150117 q = 1) (hb : d200713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150117, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150118 q = 1) (hb : d200714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150118, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150118, d200714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62118 (p : Pattern) (ha : d150123 p = 1) (hb : d200724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21480 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21510 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d200709 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150114 q = 1) (hb : d200710 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150114, d200710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21556 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150115 q = 1) (hb : d200711 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150115, d200711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150116 q = 1) (hb : d200712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150116, d200712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150117 q = 1) (hb : d200713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150117, d200713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21566 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21571 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21573 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d200719 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150119 q = 1) (hb : d200720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150119, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21580 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150120 q = 1) (hb : d200721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150120, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150121 q = 1) (hb : d200722 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150121, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150121, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150122 q = 1) (hb : d200723 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150122, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150122, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150123 q = 1) (hb : d200724 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150123, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150123, d200724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62119 (p : Pattern) (ha : d150130 p = 1) (hb : d201814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21573 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200719 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150119 q = 1) (hb : d200720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150119, d200720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21580 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150120 q = 1) (hb : d200721 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150120, d200721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150128 q = 1) (hb : d200722 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150128, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150128, d200722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150129 q = 1) (hb : d200723 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150129, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150129, d200723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150130 q = 1) (hb : d201814 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150130, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150130, d201814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62120 (p : Pattern) (ha : d150140 p = 1) (hb : d201825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150136 q = 1) (hb : d201821 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150136, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150136, d201821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21706 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150137 q = 1) (hb : d201822 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150137, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150137, d201822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150138 q = 1) (hb : d201823 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150138, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150138, d201823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150139 q = 1) (hb : d201824 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150139, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150139, d201824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150140 q = 1) (hb : d201825 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150140, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150140, d201825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62121 (p : Pattern) (ha : d150146 p = 1) (hb : d201831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21463 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150124 q = 1) (hb : d200725 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150124, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62117 q ha hb
    | true =>
      simp only [d150124, d200725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62118 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150125 q = 1) (hb : d200726 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150125, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150125, d200726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150126 q = 1) (hb : d201812 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150126, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150126, d201812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150127 q = 1) (hb : d201813 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150127, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150127, d201813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150131 q = 1) (hb : d201815 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150131, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150131, d201815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62119 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d21607 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150132 q = 1) (hb : d201816 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150132, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150132, d201816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150133 q = 1) (hb : d201817 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150133, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150133, d201817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150134 q = 1) (hb : d201818 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150134, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150134, d201818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150135 q = 1) (hb : d201819 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150135, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150135, d201819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150141 q = 1) (hb : d201826 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150141, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150141, d201826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62120 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21722 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150142 q = 1) (hb : d201827 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150142, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150142, d201827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150143 q = 1) (hb : d201828 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150143, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150143, d201828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150144 q = 1) (hb : d201829 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150144, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150144, d201829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150145 q = 1) (hb : d201830 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150145, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150145, d201830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150146 q = 1) (hb : d201831 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150146, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150146, d201831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62122 (p : Pattern) (ha : d150152 p = 1) (hb : d201837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150147 q = 1) (hb : d201832 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150147, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150147, d201832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62121 q ha hb
  have h2 (q : Pattern) (ha : d150148 q = 1) (hb : d201833 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150148, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150148, d201833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150149 q = 1) (hb : d201834 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150149, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150149, d201834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150150 q = 1) (hb : d201835 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150150, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150150, d201835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150151 q = 1) (hb : d201836 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150151, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150151, d201836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150152 q = 1) (hb : d201837 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150152, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150152, d201837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62123 (p : Pattern) (ha : d150159 p = 1) (hb : d200972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21824 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21833 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d200967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150155 q = 1) (hb : d200968 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150155, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150156 q = 1) (hb : d200969 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150156, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150157 q = 1) (hb : d200970 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150157, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150158 q = 1) (hb : d200971 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150158, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150159 q = 1) (hb : d200972 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150159, d200972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150159, d200972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62124 (p : Pattern) (ha : d150164 p = 1) (hb : d200982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21824 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d200967 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150155 q = 1) (hb : d200968 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150155, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150155, d200968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d21962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150156 q = 1) (hb : d200969 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150156, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150156, d200969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150157 q = 1) (hb : d200970 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150157, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150157, d200970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150158 q = 1) (hb : d200971 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150158, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150158, d200971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d21972 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d21977 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d21980 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d200977 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150160 q = 1) (hb : d200978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150160, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d21987 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150161 q = 1) (hb : d200979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150161, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150162 q = 1) (hb : d200980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150162, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150162, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150163 q = 1) (hb : d200981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150163, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150163, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150164 q = 1) (hb : d200982 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150164, d200982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150164, d200982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62125 (p : Pattern) (ha : d150171 p = 1) (hb : d201842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d200977 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150160 q = 1) (hb : d200978 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150160, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150160, d200978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21987 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150161 q = 1) (hb : d200979 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150161, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150161, d200979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150169 q = 1) (hb : d200980 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150169, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150169, d200980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150170 q = 1) (hb : d200981 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150170, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150170, d200981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150171 q = 1) (hb : d201842 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150171, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150171, d201842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62126 (p : Pattern) (ha : d150181 p = 1) (hb : d201853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22110 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201848 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150177 q = 1) (hb : d201849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150177, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150177, d201849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22188 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150178 q = 1) (hb : d201850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150178, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150178, d201850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150179 q = 1) (hb : d201851 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150179, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150179, d201851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150180 q = 1) (hb : d201852 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150180, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150180, d201852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150181 q = 1) (hb : d201853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150181, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150181, d201853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62127 (p : Pattern) (ha : d150187 p = 1) (hb : d201859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21816 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150165 q = 1) (hb : d200983 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150165, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62123 q ha hb
    | true =>
      simp only [d150165, d200983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62124 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22010 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150166 q = 1) (hb : d200984 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150166, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150166, d200984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150167 q = 1) (hb : d201840 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150167, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150167, d201840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150168 q = 1) (hb : d201841 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150168, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150168, d201841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150172 q = 1) (hb : d201843 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150172, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150172, d201843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62125 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22019 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150173 q = 1) (hb : d201844 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150173, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150173, d201844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150174 q = 1) (hb : d201845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150174, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150174, d201845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150175 q = 1) (hb : d201846 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150175, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150175, d201846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150176 q = 1) (hb : d201847 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150176, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150176, d201847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150182 q = 1) (hb : d201854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150182, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150182, d201854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62126 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22204 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150183 q = 1) (hb : d201855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150183, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150183, d201855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150184 q = 1) (hb : d201856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150184, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150184, d201856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150185 q = 1) (hb : d201857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150185, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150185, d201857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150186 q = 1) (hb : d201858 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150186, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150186, d201858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150187 q = 1) (hb : d201859 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150187, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150187, d201859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62128 (p : Pattern) (ha : d150193 p = 1) (hb : d201865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150188 q = 1) (hb : d201860 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150188, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150188, d201860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62127 q ha hb
  have h2 (q : Pattern) (ha : d150189 q = 1) (hb : d201861 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150189, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150189, d201861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150190 q = 1) (hb : d201862 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150190, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150190, d201862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150191 q = 1) (hb : d201863 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150191, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150191, d201863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150192 q = 1) (hb : d201864 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150192, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150192, d201864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150193 q = 1) (hb : d201865 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150193, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150193, d201865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62129 (p : Pattern) (ha : d150201 p = 1) (hb : d201251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22351 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d201246 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150197 q = 1) (hb : d201247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150197, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d22435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150198 q = 1) (hb : d201248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150198, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150199 q = 1) (hb : d201249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150199, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150200 q = 1) (hb : d201250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150200, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150201 q = 1) (hb : d201251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150201, d201251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150201, d201251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62130 (p : Pattern) (ha : d150206 p = 1) (hb : d201261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d201246 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150197 q = 1) (hb : d201247 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150197, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150197, d201247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22435 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150198 q = 1) (hb : d201248 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150198, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150198, d201248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150199 q = 1) (hb : d201249 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150199, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150199, d201249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150200 q = 1) (hb : d201250 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150200, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150200, d201250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22445 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22450 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d22453 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d201256 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150202 q = 1) (hb : d201257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150202, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22460 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150203 q = 1) (hb : d201258 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150203, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150204 q = 1) (hb : d201259 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150204, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150204, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150205 q = 1) (hb : d201260 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150205, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150205, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150206 q = 1) (hb : d201261 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150206, d201261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150206, d201261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62131 (p : Pattern) (ha : d150213 p = 1) (hb : d201871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22453 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201256 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150202 q = 1) (hb : d201257 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150202, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150202, d201257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150203 q = 1) (hb : d201258 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150203, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150203, d201258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150211 q = 1) (hb : d201259 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150211, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150211, d201259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150212 q = 1) (hb : d201260 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150212, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150212, d201260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150213 q = 1) (hb : d201871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150213, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150213, d201871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62132 (p : Pattern) (ha : d150223 p = 1) (hb : d201882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201877 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150219 q = 1) (hb : d201878 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150219, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150219, d201878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22653 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150220 q = 1) (hb : d201879 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150220, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150220, d201879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150221 q = 1) (hb : d201880 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150221, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150221, d201880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150222 q = 1) (hb : d201881 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150222, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150222, d201881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150223 q = 1) (hb : d201882 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150223, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150223, d201882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62133 (p : Pattern) (ha : d150229 p = 1) (hb : d201888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150207 q = 1) (hb : d201262 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150207, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62129 q ha hb
    | true =>
      simp only [d150207, d201262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62130 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150208 q = 1) (hb : d201263 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150208, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150208, d201263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150209 q = 1) (hb : d201869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150209, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150209, d201869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150210 q = 1) (hb : d201870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150210, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150210, d201870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150214 q = 1) (hb : d201872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150214, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150214, d201872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62131 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22492 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150215 q = 1) (hb : d201873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150215, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150215, d201873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150216 q = 1) (hb : d201874 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150216, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150216, d201874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150217 q = 1) (hb : d201875 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150217, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150217, d201875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150218 q = 1) (hb : d201876 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150218, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150218, d201876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150224 q = 1) (hb : d201883 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150224, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150224, d201883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62132 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22669 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150225 q = 1) (hb : d201884 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150225, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150225, d201884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150226 q = 1) (hb : d201885 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150226, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150226, d201885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150227 q = 1) (hb : d201886 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150227, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150227, d201886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150228 q = 1) (hb : d201887 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150228, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150228, d201887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150229 q = 1) (hb : d201888 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150229, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150229, d201888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62134 (p : Pattern) (ha : d150235 p = 1) (hb : d201894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150230 q = 1) (hb : d201889 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150230, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150230, d201889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62133 q ha hb
  have h2 (q : Pattern) (ha : d150231 q = 1) (hb : d201890 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150231, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150231, d201890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150232 q = 1) (hb : d201891 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150232, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150232, d201891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150233 q = 1) (hb : d201892 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150233, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150233, d201892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150234 q = 1) (hb : d201893 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150234, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150234, d201893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150235 q = 1) (hb : d201894 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150235, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150235, d201894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62135 (p : Pattern) (ha : d150244 p = 1) (hb : d201509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22757 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22766 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22794 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d201504 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150240 q = 1) (hb : d201505 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d150240, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d22868 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d150241 q = 1) (hb : d201506 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150241, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d150242 q = 1) (hb : d201507 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150242, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150243 q = 1) (hb : d201508 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150243, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150244 q = 1) (hb : d201509 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150244, d201509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150244, d201509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro62136 (p : Pattern) (ha : d150249 p = 1) (hb : d201519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22757 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d201504 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d150240 q = 1) (hb : d201505 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150240, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d150240, d201505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d22868 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d150241 q = 1) (hb : d201506 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150241, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150241, d201506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d150242 q = 1) (hb : d201507 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150242, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150242, d201507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150243 q = 1) (hb : d201508 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150243, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150243, d201508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d22878 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d22883 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d22886 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d201514 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d150245 q = 1) (hb : d201515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d150245, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d22893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150246 q = 1) (hb : d201516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150246, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150247 q = 1) (hb : d201517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150247, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d150247, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150248 q = 1) (hb : d201518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150248, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d150248, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150249 q = 1) (hb : d201519 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150249, d201519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150249, d201519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro62137 (p : Pattern) (ha : d150256 p = 1) (hb : d201901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22886 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201514 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150245 q = 1) (hb : d201515 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150245, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150245, d201515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22893 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150246 q = 1) (hb : d201516 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150246, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150246, d201516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150254 q = 1) (hb : d201517 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150254, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150254, d201517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150255 q = 1) (hb : d201518 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150255, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150255, d201518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150256 q = 1) (hb : d201901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150256, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150256, d201901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62138 (p : Pattern) (ha : d150266 p = 1) (hb : d201912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d22989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d201907 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150262 q = 1) (hb : d201908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150262, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150262, d201908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d23059 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150263 q = 1) (hb : d201909 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150263, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150263, d201909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d150264 q = 1) (hb : d201910 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150264, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150264, d201910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150265 q = 1) (hb : d201911 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150265, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150265, d201911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150266 q = 1) (hb : d201912 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150266, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150266, d201912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62139 (p : Pattern) (ha : d150272 p = 1) (hb : d201918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d22749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150250 q = 1) (hb : d201520 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150250, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62135 q ha hb
    | true =>
      simp only [d150250, d201520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62136 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22916 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150251 q = 1) (hb : d201521 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150251, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150251, d201521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150252 q = 1) (hb : d201899 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150252, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150252, d201899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150253 q = 1) (hb : d201900 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150253, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150253, d201900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150257 q = 1) (hb : d201902 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150257, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150257, d201902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62137 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d22925 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d150258 q = 1) (hb : d201903 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150258, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150258, d201903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d150259 q = 1) (hb : d201904 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150259, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150259, d201904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150260 q = 1) (hb : d201905 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150260, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150260, d201905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d150261 q = 1) (hb : d201906 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150261, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150261, d201906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150267 q = 1) (hb : d201913 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150267, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150267, d201913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62138 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d23075 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d150268 q = 1) (hb : d201914 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150268, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150268, d201914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d150269 q = 1) (hb : d201915 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150269, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150269, d201915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150270 q = 1) (hb : d201916 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150270, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150270, d201916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d150271 q = 1) (hb : d201917 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150271, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150271, d201917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d150272 q = 1) (hb : d201918 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150272, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150272, d201918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro62140 (p : Pattern) (ha : d150278 p = 1) (hb : d201924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150273 q = 1) (hb : d201919 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150273, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150273, d201919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62139 q ha hb
  have h2 (q : Pattern) (ha : d150274 q = 1) (hb : d201920 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150274, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150274, d201920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150275 q = 1) (hb : d201921 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150275, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150275, d201921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150276 q = 1) (hb : d201922 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150276, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150276, d201922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150277 q = 1) (hb : d201923 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150277, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150277, d201923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150278 q = 1) (hb : d201924 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150278, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150278, d201924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62141 (p : Pattern) (ha : d150284 p = 1) (hb : d201930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d150113 q = 1) (hb : d201811 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150113, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62110 q ha hb
    | true =>
      simp only [d150113, d201811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62116 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150153 q = 1) (hb : d201838 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150153, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150153, d201838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62122 q ha hb
  have h3 (q : Pattern) (ha : d150154 q = 1) (hb : d201839 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150154, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150154, d201839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150194 q = 1) (hb : d201866 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150194, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150194, d201866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62128 q ha hb
  have h5 (q : Pattern) (ha : d150195 q = 1) (hb : d201867 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150195, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150195, d201867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150196 q = 1) (hb : d201868 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150196, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150196, d201868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150236 q = 1) (hb : d201895 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150236, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150236, d201895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62134 q ha hb
  have h8 (q : Pattern) (ha : d150237 q = 1) (hb : d201896 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150237, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150237, d201896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150238 q = 1) (hb : d201897 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150238, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150238, d201897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150239 q = 1) (hb : d201898 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150239, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150239, d201898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150279 q = 1) (hb : d201925 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150279, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150279, d201925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62140 q ha hb
  have h12 (q : Pattern) (ha : d150280 q = 1) (hb : d201926 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150280, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150280, d201926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150281 q = 1) (hb : d201927 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150281, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150281, d201927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150282 q = 1) (hb : d201928 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150282, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150282, d201928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150283 q = 1) (hb : d201929 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150283, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150283, d201929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150284 q = 1) (hb : d201930 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150284, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150284, d201930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro62142 (p : Pattern) (ha : d150290 p = 1) (hb : d201936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150285 q = 1) (hb : d201931 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150285, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62141 q ha hb
    | true =>
      simp only [d150285, d201931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150286 q = 1) (hb : d201932 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150286, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150286, d201932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150287 q = 1) (hb : d201933 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150287, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150287, d201933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150288 q = 1) (hb : d201934 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150288, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150288, d201934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150289 q = 1) (hb : d201935 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150289, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150289, d201935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150290 q = 1) (hb : d201936 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150290, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150290, d201936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62143 (p : Pattern) (ha : d150296 p = 1) (hb : d201942 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150291 q = 1) (hb : d201937 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150291, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62142 q ha hb
    | true =>
      simp only [d150291, d201937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150292 q = 1) (hb : d201938 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150292, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150292, d201938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150293 q = 1) (hb : d201939 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150293, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150293, d201939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150294 q = 1) (hb : d201940 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150294, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150294, d201940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150295 q = 1) (hb : d201941 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150295, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150295, d201941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150296 q = 1) (hb : d201942 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150296, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150296, d201942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62144 (p : Pattern) (ha : d150302 p = 1) (hb : d201948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150297 q = 1) (hb : d201943 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150297, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62143 q ha hb
    | true =>
      simp only [d150297, d201943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150298 q = 1) (hb : d201944 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150298, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150298, d201944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150299 q = 1) (hb : d201945 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150299, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150299, d201945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150300 q = 1) (hb : d201946 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150300, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150300, d201946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150301 q = 1) (hb : d201947 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150301, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150301, d201947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150302 q = 1) (hb : d201948 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150302, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150302, d201948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62145 (p : Pattern) (ha : d150308 p = 1) (hb : d201954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150303 q = 1) (hb : d201949 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150303, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62144 q ha hb
    | true =>
      simp only [d150303, d201949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150304 q = 1) (hb : d201950 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150304, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150304, d201950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150305 q = 1) (hb : d201951 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150305, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150305, d201951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150306 q = 1) (hb : d201952 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150306, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150306, d201952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150307 q = 1) (hb : d201953 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150307, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150307, d201953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150308 q = 1) (hb : d201954 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150308, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150308, d201954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62146 (p : Pattern) (ha : d150314 p = 1) (hb : d201960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150309 q = 1) (hb : d201955 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150309, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62145 q ha hb
    | true =>
      simp only [d150309, d201955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150310 q = 1) (hb : d201956 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150310, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150310, d201956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150311 q = 1) (hb : d201957 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150311, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150311, d201957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150312 q = 1) (hb : d201958 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150312, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150312, d201958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150313 q = 1) (hb : d201959 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150313, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150313, d201959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150314 q = 1) (hb : d201960 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150314, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150314, d201960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62147 (p : Pattern) (ha : d150320 p = 1) (hb : d201966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150315 q = 1) (hb : d201961 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150315, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62146 q ha hb
    | true =>
      simp only [d150315, d201961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150316 q = 1) (hb : d201962 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150316, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150316, d201962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150317 q = 1) (hb : d201963 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150317, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150317, d201963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150318 q = 1) (hb : d201964 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150318, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150318, d201964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150319 q = 1) (hb : d201965 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150319, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150319, d201965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150320 q = 1) (hb : d201966 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150320, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150320, d201966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62148 (p : Pattern) (ha : d150326 p = 1) (hb : d201972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150321 q = 1) (hb : d201967 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150321, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62147 q ha hb
    | true =>
      simp only [d150321, d201967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150322 q = 1) (hb : d201968 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150322, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150322, d201968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150323 q = 1) (hb : d201969 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150323, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150323, d201969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150324 q = 1) (hb : d201970 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150324, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150324, d201970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150325 q = 1) (hb : d201971 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150325, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150325, d201971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150326 q = 1) (hb : d201972 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150326, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150326, d201972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62149 (p : Pattern) (ha : d25104 p = 1) (hb : d152854 p = 1) : d156536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25103 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23 q = 1) (hb : d152852 q = 1) : d23 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25104 q = 1) (hb : d152854 q = 1) : d156536 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25104, d152854, d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25104, d152854, d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62150 (p : Pattern) (ha : d25110 p = 1) (hb : d152855 p = 1) : d156542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25105 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62149 q ha hb
    | true =>
      simp only [d25105, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25106 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25106, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25107 q = 1) (hb : d152854 q = 1) : d156539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25108 q = 1) (hb : d152854 q = 1) : d156540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25108, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25109 q = 1) (hb : d152854 q = 1) : d156541 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25109, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25109, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25110 q = 1) (hb : d152855 q = 1) : d156542 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25110, d152855, d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25110, d152855, d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62151 (p : Pattern) (ha : d25116 p = 1) (hb : d152855 p = 1) : d156548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25111 q = 1) (hb : d152855 q = 1) : d156543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62150 q ha hb
    | true =>
      simp only [d25111, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
  have h2 (q : Pattern) (ha : d25112 q = 1) (hb : d152855 q = 1) : d156544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25113 q = 1) (hb : d152855 q = 1) : d156545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25114 q = 1) (hb : d152855 q = 1) : d156546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25114, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25115 q = 1) (hb : d152855 q = 1) : d156547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25115, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25115, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25116 q = 1) (hb : d152855 q = 1) : d156548 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25116, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25116, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62152 (p : Pattern) (ha : d25122 p = 1) (hb : d152855 p = 1) : d156554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62151 q ha hb
    | true =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25121 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25121, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25122 q = 1) (hb : d152855 q = 1) : d156554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25122, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25122, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62153 (p : Pattern) (ha : d152855 p = 1) (hb : d201977 p = 1) : d156560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30064 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30065 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25123 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62152 q ha hb
    | true =>
      simp only [d25123, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d201973 q = 1) : d156556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d201973, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d201974 q = 1) : d156557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201974, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d201975 q = 1) : d156558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d201975, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d201976 q = 1) : d156559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d201976, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d201977 q = 1) : d156560 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201977, d156560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201977, d156560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62154 (p : Pattern) (ha : d25129 p = 1) (hb : d152855 p = 1) : d156561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62151 q ha hb
    | true =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25121 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25121, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25121, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25129 q = 1) (hb : d152855 q = 1) : d156561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25129, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25129, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62155 (p : Pattern) (ha : d152855 p = 1) (hb : d201982 p = 1) : d156567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30064 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30065 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25123 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62152 q ha hb
    | true =>
      simp only [d25123, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d201973 q = 1) : d156556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201973, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d201973, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d201974 q = 1) : d156557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201974, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d201974, d156557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d201975 q = 1) : d156558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201975, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d201975, d156558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d201976 q = 1) : d156559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201976, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d201976, d156559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30071 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30072 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25130 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62154 q ha hb
    | true =>
      simp only [d25130, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d201978 q = 1) : d156563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d201978, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d152855 q = 1) (hb : d201979 q = 1) : d156564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d201979, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d152855 q = 1) (hb : d201980 q = 1) : d156565 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201980, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d201980, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d152855 q = 1) (hb : d201981 q = 1) : d156566 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201981, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d201981, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d152855 q = 1) (hb : d201982 q = 1) : d156567 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201982, d156567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d201982, d156567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro62156 (p : Pattern) (ha : d152855 p = 1) (hb : d201989 p = 1) : d156572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25130 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62154 q ha hb
    | true =>
      simp only [d25130, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d201978 q = 1) : d156563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201978, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d201978, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d201979 q = 1) : d156564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201979, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201979, d156564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d201987 q = 1) : d156565 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201987, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201987, d156565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d201988 q = 1) : d156566 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201988, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201988, d156566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d201989 q = 1) : d156572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201989, d156572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201989, d156572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62157 (p : Pattern) (ha : d25153 p = 1) (hb : d152855 p = 1) : d156583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25148 q = 1) (hb : d152854 q = 1) : d156578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62149 q ha hb
  have h2 (q : Pattern) (ha : d25105 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62149 q ha hb
    | true =>
      simp only [d25105, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25149 q = 1) (hb : d152854 q = 1) : d156579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25149, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25106 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25106, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25150 q = 1) (hb : d152854 q = 1) : d156580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25150, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25151 q = 1) (hb : d152854 q = 1) : d156581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25151, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25152 q = 1) (hb : d152854 q = 1) : d156582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25152, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25152, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25153 q = 1) (hb : d152855 q = 1) : d156583 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25153, d152855, d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25153, d152855, d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62158 (p : Pattern) (ha : d25159 p = 1) (hb : d152855 p = 1) : d156589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25154 q = 1) (hb : d152855 q = 1) : d156584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62157 q ha hb
    | true =>
      simp only [d25154, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
  have h2 (q : Pattern) (ha : d25155 q = 1) (hb : d152855 q = 1) : d156585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25156 q = 1) (hb : d152855 q = 1) : d156586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d72 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d73 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25157 q = 1) (hb : d152855 q = 1) : d156587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25157, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25158 q = 1) (hb : d152855 q = 1) : d156588 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25158, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25158, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25159 q = 1) (hb : d152855 q = 1) : d156589 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25159, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25159, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62159 (p : Pattern) (ha : d25165 p = 1) (hb : d152855 p = 1) : d156595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d152855 q = 1) : d156590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62158 q ha hb
    | true =>
      simp only [d25160, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d152855 q = 1) : d156591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30057 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25162 q = 1) (hb : d152855 q = 1) : d156592 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25162, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25162, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25163 q = 1) (hb : d152855 q = 1) : d156593 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25163, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25163, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25164 q = 1) (hb : d152855 q = 1) : d156594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25164, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25164, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25165 q = 1) (hb : d152855 q = 1) : d156595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25165, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25165, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62160 (p : Pattern) (ha : d152855 p = 1) (hb : d201999 p = 1) : d156601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25166 q = 1) (hb : d152855 q = 1) : d156596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25166, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62159 q ha hb
    | true =>
      simp only [d25166, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30058 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d201995 q = 1) : d156597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201995, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d201995, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30058 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d201996 q = 1) : d156598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d201996, d156598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d201996, d156598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d201997 q = 1) : d156599 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d201997, d156599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201997, d156599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d201998 q = 1) : d156600 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d201998, d156600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201998, d156600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d201999 q = 1) : d156601 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d201999, d156601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201999, d156601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62161 (p : Pattern) (ha : d152855 p = 1) (hb : d202005 p = 1) : d156607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30061 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30061 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30062 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d201983 q = 1) : d156568 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201983, d156568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62153 q ha hb
    | true =>
      simp only [d201983, d156568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62155 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30063 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d201984 q = 1) : d156569 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201984, d156569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d201984, d156569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d201985 q = 1) : d156570 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201985, d156570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d201985, d156570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d201986 q = 1) : d156571 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201986, d156571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d201986, d156571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d201990 q = 1) : d156573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d201990, d156573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d201990, d156573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62156 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d201991 q = 1) : d156574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d201991, d156574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d201991, d156574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d201992 q = 1) : d156575 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d201992, d156575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d201992, d156575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d201993 q = 1) : d156576 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d201993, d156576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d201993, d156576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d201994 q = 1) : d156577 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d201994, d156577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d201994, d156577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d152855 q = 1) (hb : d202000 q = 1) : d156602 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202000, d156602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202000, d156602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62160 q ha hb
  have h17 (q : Pattern) (ha : d152855 q = 1) (hb : d202001 q = 1) : d156603 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202001, d156603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202001, d156603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d152855 q = 1) (hb : d202002 q = 1) : d156604 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202002, d156604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202002, d156604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d152855 q = 1) (hb : d202003 q = 1) : d156605 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202003, d156605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202003, d156605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d152855 q = 1) (hb : d202004 q = 1) : d156606 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202004, d156606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202004, d156606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d152855 q = 1) (hb : d202005 q = 1) : d156607 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202005, d156607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202005, d156607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro62162 (p : Pattern) (ha : d25187 p = 1) (hb : d152855 p = 1) : d156617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25123 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62152 q ha hb
    | true =>
      simp only [d25123, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
  have h2 (q : Pattern) (ha : d25183 q = 1) (hb : d152855 q = 1) : d156613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25184 q = 1) (hb : d152855 q = 1) : d156614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25184, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25185 q = 1) (hb : d152855 q = 1) : d156615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25186 q = 1) (hb : d152855 q = 1) : d156616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25187 q = 1) (hb : d152855 q = 1) : d156617 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25187, d156617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25187, d156617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62163 (p : Pattern) (ha : d25194 p = 1) (hb : d152855 p = 1) : d156624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25123 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62152 q ha hb
    | true =>
      simp only [d25123, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
  have h2 (q : Pattern) (ha : d25183 q = 1) (hb : d152855 q = 1) : d156613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25184 q = 1) (hb : d152855 q = 1) : d156614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25184, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25185 q = 1) (hb : d152855 q = 1) : d156615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25186 q = 1) (hb : d152855 q = 1) : d156616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25130 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25130, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62154 q ha hb
    | true =>
      simp only [d25130, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
  have h7 (q : Pattern) (ha : d25190 q = 1) (hb : d152855 q = 1) : d156620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25190, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25190, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25191 q = 1) (hb : d152855 q = 1) : d156621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25191, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25191, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25192 q = 1) (hb : d152855 q = 1) : d156622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25192, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25192, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25193 q = 1) (hb : d152855 q = 1) : d156623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25193, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25193, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25194 q = 1) (hb : d152855 q = 1) : d156624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25194, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25194, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62164 (p : Pattern) (ha : d25296 p = 1) (hb : d152855 p = 1) : d156682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25123 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25123, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62152 q ha hb
    | true =>
      simp only [d25123, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
  have h2 (q : Pattern) (ha : d25183 q = 1) (hb : d152855 q = 1) : d156613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25183, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25183, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25184 q = 1) (hb : d152855 q = 1) : d156614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25184, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25184, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25185 q = 1) (hb : d152855 q = 1) : d156615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25185, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25185, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25186 q = 1) (hb : d152855 q = 1) : d156616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25186, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25186, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30051 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25296 q = 1) (hb : d152855 q = 1) : d156682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25296, d156682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25296, d156682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62165 (p : Pattern) (ha : d25199 p = 1) (hb : d152855 p = 1) : d156629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62151 q ha hb
    | true =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25198 q = 1) (hb : d152855 q = 1) : d156628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25199 q = 1) (hb : d152855 q = 1) : d156629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25199, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25199, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62166 (p : Pattern) (ha : d25206 p = 1) (hb : d152855 p = 1) : d156636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62151 q ha hb
    | true =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25204 q = 1) (hb : d152855 q = 1) : d156634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25205 q = 1) (hb : d152855 q = 1) : d156635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25205, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25206 q = 1) (hb : d152855 q = 1) : d156636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25206, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25206, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62167 (p : Pattern) (ha : d25213 p = 1) (hb : d152854 p = 1) : d156640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25103 q = 1) (hb : d152852 q = 1) : d25103 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25213 q = 1) (hb : d152854 q = 1) : d156640 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25213, d152854, d156640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25213, d152854, d156640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62168 (p : Pattern) (ha : d25227 p = 1) (hb : d152855 p = 1) : d156646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25214 q = 1) (hb : d152854 q = 1) : d156641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62167 q ha hb
    | true =>
      simp only [d25214, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25215 q = 1) (hb : d152854 q = 1) : d156642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25215, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25216 q = 1) (hb : d152854 q = 1) : d156643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25216, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25216, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25217 q = 1) (hb : d152854 q = 1) : d156644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25217, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25217, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25105 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62149 q ha hb
    | true =>
      simp only [d25105, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25106 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25106, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25107 q = 1) (hb : d152854 q = 1) : d156539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25107, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25107, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25108 q = 1) (hb : d152854 q = 1) : d156540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25108, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25108, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25218 q = 1) (hb : d152854 q = 1) : d156645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25218, d156645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25218, d156645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25226 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25227 q = 1) (hb : d152855 q = 1) : d156646 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25227, d152855, d156646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25227, d152855, d156646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62169 (p : Pattern) (ha : d25233 p = 1) (hb : d152855 p = 1) : d156652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d152855 q = 1) : d156647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62168 q ha hb
    | true =>
      simp only [d25228, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62150 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d152855 q = 1) : d156648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d152855 q = 1) : d156649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25111 q = 1) (hb : d152855 q = 1) : d156543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62150 q ha hb
    | true =>
      simp only [d25111, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
  have h5 (q : Pattern) (ha : d25112 q = 1) (hb : d152855 q = 1) : d156544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25113 q = 1) (hb : d152855 q = 1) : d156545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25231 q = 1) (hb : d152855 q = 1) : d156650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25114 q = 1) (hb : d152855 q = 1) : d156546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25114, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25114, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25232 q = 1) (hb : d152855 q = 1) : d156651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25232, d156651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25232, d156651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25233 q = 1) (hb : d152855 q = 1) : d156652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25233, d156652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25233, d156652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro62170 (p : Pattern) (ha : d25239 p = 1) (hb : d152855 p = 1) : d156658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62169 q ha hb
    | true =>
      simp only [d25234, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62151 q ha hb
    | true =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d152855 q = 1) : d156657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25239 q = 1) (hb : d152855 q = 1) : d156658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25239, d156658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25239, d156658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62171 (p : Pattern) (ha : d25267 p = 1) (hb : d152855 p = 1) : d156554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62151 q ha hb
    | true =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25267 q = 1) (hb : d152855 q = 1) : d156554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25267, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25267, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62172 (p : Pattern) (ha : d152855 p = 1) (hb : d202015 p = 1) : d156664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25200 q = 1) (hb : d152855 q = 1) : d156630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62165 q ha hb
    | true =>
      simp only [d25200, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30064 q ha hb
  have h2 (q : Pattern) (ha : d25201 q = 1) (hb : d152855 q = 1) : d156631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25202 q = 1) (hb : d152855 q = 1) : d156632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25202, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25203 q = 1) (hb : d152855 q = 1) : d156633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25207 q = 1) (hb : d152855 q = 1) : d156637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62166 q ha hb
    | true =>
      simp only [d25207, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30065 q ha hb
  have h6 (q : Pattern) (ha : d25208 q = 1) (hb : d152855 q = 1) : d156638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25209 q = 1) (hb : d152855 q = 1) : d156639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25209, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25240 q = 1) (hb : d152855 q = 1) : d156659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62170 q ha hb
    | true =>
      simp only [d25240, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62152 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202011 q = 1) : d156660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202011, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d25268 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62171 q ha hb
    | true =>
      simp only [d25268, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25269 q = 1) (hb : d152855 q = 1) : d156556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25269, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202012 q = 1) : d156661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202012, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202013 q = 1) : d156662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202013, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202014 q = 1) : d156663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202014, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202015 q = 1) : d156664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202015, d156664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202015, d156664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62173 (p : Pattern) (ha : d25274 p = 1) (hb : d152855 p = 1) : d156665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62151 q ha hb
    | true =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25120 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25120, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25120, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25198 q = 1) (hb : d152855 q = 1) : d156628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25198, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25198, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25274 q = 1) (hb : d152855 q = 1) : d156665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25274, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25274, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62174 (p : Pattern) (ha : d25279 p = 1) (hb : d152855 p = 1) : d156670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62151 q ha hb
    | true =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30050 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25119 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25119, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25204 q = 1) (hb : d152855 q = 1) : d156634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25204, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25204, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25205 q = 1) (hb : d152855 q = 1) : d156635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25205, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25205, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25279 q = 1) (hb : d152855 q = 1) : d156670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25279, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25279, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62175 (p : Pattern) (ha : d25283 p = 1) (hb : d152855 p = 1) : d156674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25234 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25234, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62169 q ha hb
    | true =>
      simp only [d25234, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25235 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25235, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25235, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25117 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62151 q ha hb
    | true =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25118 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25236 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25236, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25236, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25237 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25237, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25237, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25238 q = 1) (hb : d152855 q = 1) : d156657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25238, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25238, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25283 q = 1) (hb : d152855 q = 1) : d156674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25283, d156674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25283, d156674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62176 (p : Pattern) (ha : d25288 p = 1) (hb : d152855 p = 1) : d156561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25117 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62151 q ha hb
    | true =>
      simp only [d25117, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25118 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25118, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25264 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25264, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25264, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25265 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25265, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25265, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25266 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25266, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25266, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25288 q = 1) (hb : d152855 q = 1) : d156561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25288, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25288, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62177 (p : Pattern) (ha : d152855 p = 1) (hb : d202020 p = 1) : d156680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25200 q = 1) (hb : d152855 q = 1) : d156630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25200, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62165 q ha hb
    | true =>
      simp only [d25200, d156630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30064 q ha hb
  have h2 (q : Pattern) (ha : d25201 q = 1) (hb : d152855 q = 1) : d156631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25201, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25201, d156631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25202 q = 1) (hb : d152855 q = 1) : d156632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25202, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25202, d156632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25203 q = 1) (hb : d152855 q = 1) : d156633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25203, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25203, d156633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25207 q = 1) (hb : d152855 q = 1) : d156637 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25207, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62166 q ha hb
    | true =>
      simp only [d25207, d156637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30065 q ha hb
  have h6 (q : Pattern) (ha : d25208 q = 1) (hb : d152855 q = 1) : d156638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25208, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25208, d156638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25209 q = 1) (hb : d152855 q = 1) : d156639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25209, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25209, d156639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25240 q = 1) (hb : d152855 q = 1) : d156659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25240, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62170 q ha hb
    | true =>
      simp only [d25240, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62152 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202011 q = 1) : d156660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202011, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202011, d156660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d25268 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25268, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62171 q ha hb
    | true =>
      simp only [d25268, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25269 q = 1) (hb : d152855 q = 1) : d156556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25269, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25269, d156556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202012 q = 1) : d156661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202012, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202012, d156661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202013 q = 1) : d156662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202013, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202013, d156662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202014 q = 1) : d156663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202014, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202014, d156663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25275 q = 1) (hb : d152855 q = 1) : d156666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25275, d156666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62173 q ha hb
    | true =>
      simp only [d25275, d156666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30071 q ha hb
  have h16 (q : Pattern) (ha : d25276 q = 1) (hb : d152855 q = 1) : d156667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25276, d156667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25276, d156667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25277 q = 1) (hb : d152855 q = 1) : d156668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25277, d156668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25277, d156668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25278 q = 1) (hb : d152855 q = 1) : d156669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25278, d156669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25278, d156669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25280 q = 1) (hb : d152855 q = 1) : d156671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25280, d156671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62174 q ha hb
    | true =>
      simp only [d25280, d156671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30072 q ha hb
  have h20 (q : Pattern) (ha : d25281 q = 1) (hb : d152855 q = 1) : d156672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25281, d156672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25281, d156672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25282 q = 1) (hb : d152855 q = 1) : d156673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25282, d156673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25282, d156673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25284 q = 1) (hb : d152855 q = 1) : d156675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62175 q ha hb
    | true =>
      simp only [d25284, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62154 q ha hb
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202016 q = 1) : d156676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d202016, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d25289 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62176 q ha hb
    | true =>
      simp only [d25289, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25290 q = 1) (hb : d152855 q = 1) : d156563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25290, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d152855 q = 1) (hb : d202017 q = 1) : d156677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202017, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d152855 q = 1) (hb : d202018 q = 1) : d156678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202018, d156678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d202018, d156678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d152855 q = 1) (hb : d202019 q = 1) : d156679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202019, d156679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d202019, d156679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d152855 q = 1) (hb : d202020 q = 1) : d156680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202020, d156680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202020, d156680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro62178 (p : Pattern) (ha : d152855 p = 1) (hb : d202027 p = 1) : d156689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25284 q = 1) (hb : d152855 q = 1) : d156675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25284, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62175 q ha hb
    | true =>
      simp only [d25284, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62154 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202016 q = 1) : d156676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202016, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202016, d156676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d25289 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25289, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62176 q ha hb
    | true =>
      simp only [d25289, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25290 q = 1) (hb : d152855 q = 1) : d156563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25290, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25290, d156563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202017 q = 1) : d156677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202017, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202017, d156677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202025 q = 1) : d156687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202025, d156687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202025, d156687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202026 q = 1) : d156688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202026, d156688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202026, d156688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202027 q = 1) : d156689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202027, d156689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202027, d156689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62179 (p : Pattern) (ha : d25319 p = 1) (hb : d152855 p = 1) : d156700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25309 q = 1) (hb : d152854 q = 1) : d156695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25309, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25309, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62167 q ha hb
  have h2 (q : Pattern) (ha : d25214 q = 1) (hb : d152854 q = 1) : d156641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62167 q ha hb
    | true =>
      simp only [d25214, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25310 q = 1) (hb : d152854 q = 1) : d156696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25310, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25310, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25215 q = 1) (hb : d152854 q = 1) : d156642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25215, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25311 q = 1) (hb : d152854 q = 1) : d156697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25311, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25311, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25312 q = 1) (hb : d152854 q = 1) : d156698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25312, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25312, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25148 q = 1) (hb : d152854 q = 1) : d156578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25148, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25148, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62149 q ha hb
  have h8 (q : Pattern) (ha : d25105 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25105, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62149 q ha hb
    | true =>
      simp only [d25105, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25149 q = 1) (hb : d152854 q = 1) : d156579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25149, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25149, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25106 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25106, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25106, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25150 q = 1) (hb : d152854 q = 1) : d156580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25150, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25150, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25151 q = 1) (hb : d152854 q = 1) : d156581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25151, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25151, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25313 q = 1) (hb : d152854 q = 1) : d156699 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25313, d156699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25313, d156699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25318 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25319 q = 1) (hb : d152855 q = 1) : d156700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25319, d152855, d156700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25319, d152855, d156700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62180 (p : Pattern) (ha : d25325 p = 1) (hb : d152855 p = 1) : d156706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25320 q = 1) (hb : d152855 q = 1) : d156701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62179 q ha hb
    | true =>
      simp only [d25320, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62157 q ha hb
  have h2 (q : Pattern) (ha : d25321 q = 1) (hb : d152855 q = 1) : d156702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25322 q = 1) (hb : d152855 q = 1) : d156703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25154 q = 1) (hb : d152855 q = 1) : d156584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62157 q ha hb
    | true =>
      simp only [d25154, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
  have h5 (q : Pattern) (ha : d25155 q = 1) (hb : d152855 q = 1) : d156585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25156 q = 1) (hb : d152855 q = 1) : d156586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25323 q = 1) (hb : d152855 q = 1) : d156704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25323, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25157 q = 1) (hb : d152855 q = 1) : d156587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25157, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25157, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25324 q = 1) (hb : d152855 q = 1) : d156705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25324, d156705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25324, d156705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25325 q = 1) (hb : d152855 q = 1) : d156706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25325, d156706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25325, d156706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro62181 (p : Pattern) (ha : d25331 p = 1) (hb : d152855 p = 1) : d156712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25326 q = 1) (hb : d152855 q = 1) : d156707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25326, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62180 q ha hb
    | true =>
      simp only [d25326, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25327 q = 1) (hb : d152855 q = 1) : d156708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25327, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25327, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25160 q = 1) (hb : d152855 q = 1) : d156590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62158 q ha hb
    | true =>
      simp only [d25160, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25161 q = 1) (hb : d152855 q = 1) : d156591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25328 q = 1) (hb : d152855 q = 1) : d156709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25328, d156709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25328, d156709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25329 q = 1) (hb : d152855 q = 1) : d156710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25329, d156710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25329, d156710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25330 q = 1) (hb : d152855 q = 1) : d156711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25330, d156711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25330, d156711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25331 q = 1) (hb : d152855 q = 1) : d156712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25331, d156712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25331, d156712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62182 (p : Pattern) (ha : d25356 p = 1) (hb : d152855 p = 1) : d156595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25160 q = 1) (hb : d152855 q = 1) : d156590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25160, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62158 q ha hb
    | true =>
      simp only [d25160, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25161 q = 1) (hb : d152855 q = 1) : d156591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25161, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25161, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25353 q = 1) (hb : d152855 q = 1) : d156592 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25353, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25353, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25354 q = 1) (hb : d152855 q = 1) : d156593 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25354, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25354, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25355 q = 1) (hb : d152855 q = 1) : d156594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25355, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25355, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25356 q = 1) (hb : d152855 q = 1) : d156595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25356, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25356, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62183 (p : Pattern) (ha : d152855 p = 1) (hb : d202037 p = 1) : d156718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25332 q = 1) (hb : d152855 q = 1) : d156713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25332, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62181 q ha hb
    | true =>
      simp only [d25332, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62159 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202033 q = 1) : d156714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202033, d156714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202033, d156714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d25357 q = 1) (hb : d152855 q = 1) : d156596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25357, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62182 q ha hb
    | true =>
      simp only [d25357, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25358 q = 1) (hb : d152855 q = 1) : d156597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25358, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25358, d156597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202034 q = 1) : d156715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202034, d156715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202034, d156715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202035 q = 1) : d156716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202035, d156716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202035, d156716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202036 q = 1) : d156717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202036, d156717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202036, d156717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202037 q = 1) : d156718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202037, d156718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202037, d156718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62184 (p : Pattern) (ha : d152855 p = 1) (hb : d202043 p = 1) : d156724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25188 q = 1) (hb : d152855 q = 1) : d156618 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25188, d156618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25188, d156618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62162 q ha hb
  have h2 (q : Pattern) (ha : d25189 q = 1) (hb : d152855 q = 1) : d156619 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25189, d156619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25189, d156619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25195 q = 1) (hb : d152855 q = 1) : d156625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25195, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62162 q ha hb
    | true =>
      simp only [d25195, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62163 q ha hb
  have h4 (q : Pattern) (ha : d25196 q = 1) (hb : d152855 q = 1) : d156626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25196, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25196, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25197 q = 1) (hb : d152855 q = 1) : d156627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25197, d156627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25197, d156627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202021 q = 1) : d156681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202021, d156681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62172 q ha hb
    | true =>
      simp only [d202021, d156681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62177 q ha hb
  have h7 (q : Pattern) (ha : d25297 q = 1) (hb : d152855 q = 1) : d156683 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25297, d156683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62164 q ha hb
    | true =>
      simp only [d25297, d156683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30062 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202022 q = 1) : d156684 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202022, d156684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202022, d156684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202023 q = 1) : d156685 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202023, d156685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202023, d156685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d202024 q = 1) : d156686 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202024, d156686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d202024, d156686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d202028 q = 1) : d156690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202028, d156690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202028, d156690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62178 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30081 q ha hb
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202029 q = 1) : d156691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202029, d156691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202029, d156691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202030 q = 1) : d156692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202030, d156692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202030, d156692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202031 q = 1) : d156693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202031, d156693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202031, d156693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d152855 q = 1) (hb : d202032 q = 1) : d156694 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202032, d156694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202032, d156694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d152855 q = 1) (hb : d202038 q = 1) : d156719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202038, d156719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202038, d156719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62183 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30082 q ha hb
  have h19 (q : Pattern) (ha : d152855 q = 1) (hb : d202039 q = 1) : d156720 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202039, d156720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202039, d156720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d152855 q = 1) (hb : d202040 q = 1) : d156721 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202040, d156721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202040, d156721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d152855 q = 1) (hb : d202041 q = 1) : d156722 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202041, d156722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202041, d156722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d152855 q = 1) (hb : d202042 q = 1) : d156723 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202042, d156723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202042, d156723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202043 q = 1) : d156724 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202043, d156724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202043, d156724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62185 (p : Pattern) (ha : d152855 p = 1) (hb : d202049 p = 1) : d156730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30060 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202006 q = 1) : d156608 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202006, d156608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202006, d156608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62161 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202007 q = 1) : d156609 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202007, d156609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202007, d156609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202008 q = 1) : d156610 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202008, d156610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202008, d156610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202009 q = 1) : d156611 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202009, d156611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202009, d156611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202010 q = 1) : d156612 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202010, d156612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202010, d156612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d202044 q = 1) : d156725 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202044, d156725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202044, d156725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62184 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d202045 q = 1) : d156726 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202045, d156726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202045, d156726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202046 q = 1) : d156727 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202046, d156727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202046, d156727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202047 q = 1) : d156728 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202047, d156728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202047, d156728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202048 q = 1) : d156729 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202048, d156729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202048, d156729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202049 q = 1) : d156730 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202049, d156730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202049, d156730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62186 (p : Pattern) (ha : d25377 p = 1) (hb : d152855 p = 1) : d156652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25228 q = 1) (hb : d152855 q = 1) : d156647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62168 q ha hb
    | true =>
      simp only [d25228, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62150 q ha hb
  have h2 (q : Pattern) (ha : d25229 q = 1) (hb : d152855 q = 1) : d156648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25230 q = 1) (hb : d152855 q = 1) : d156649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25111 q = 1) (hb : d152855 q = 1) : d156543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62150 q ha hb
    | true =>
      simp only [d25111, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
  have h5 (q : Pattern) (ha : d25112 q = 1) (hb : d152855 q = 1) : d156544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25113 q = 1) (hb : d152855 q = 1) : d156545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25231 q = 1) (hb : d152855 q = 1) : d156650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25231, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25375 q = 1) (hb : d152855 q = 1) : d156546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25375, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25376 q = 1) (hb : d152855 q = 1) : d156651 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25376, d156651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25376, d156651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25377 q = 1) (hb : d152855 q = 1) : d156652 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25377, d156652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25377, d156652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62187 (p : Pattern) (ha : d25381 p = 1) (hb : d152855 p = 1) : d156548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25111 q = 1) (hb : d152855 q = 1) : d156543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62150 q ha hb
    | true =>
      simp only [d25111, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
  have h2 (q : Pattern) (ha : d25112 q = 1) (hb : d152855 q = 1) : d156544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25113 q = 1) (hb : d152855 q = 1) : d156545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25375 q = 1) (hb : d152855 q = 1) : d156546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25375, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25375, d156546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25380 q = 1) (hb : d152855 q = 1) : d156547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25380, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25380, d156547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25381 q = 1) (hb : d152855 q = 1) : d156548 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25381, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25381, d156548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62188 (p : Pattern) (ha : d25387 p = 1) (hb : d152855 p = 1) : d156658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62186 q ha hb
    | true =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d152855 q = 1) : d156657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25387 q = 1) (hb : d152855 q = 1) : d156658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25387, d156658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25387, d156658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62189 (p : Pattern) (ha : d25391 p = 1) (hb : d152855 p = 1) : d156554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25391 q = 1) (hb : d152855 q = 1) : d156554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25391, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25391, d156554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62190 (p : Pattern) (ha : d25397 p = 1) (hb : d152855 p = 1) : d156735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d152855 q = 1) : d156659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62188 q ha hb
    | true =>
      simp only [d25392, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62189 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d152855 q = 1) : d156731 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d152855 q = 1) : d156732 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d152855 q = 1) : d156733 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d152855 q = 1) : d156734 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25397 q = 1) (hb : d152855 q = 1) : d156735 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25397, d156735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25397, d156735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62191 (p : Pattern) (ha : d25400 p = 1) (hb : d152855 p = 1) : d156674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62186 q ha hb
    | true =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25386 q = 1) (hb : d152855 q = 1) : d156657 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25386, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25386, d156657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25400 q = 1) (hb : d152855 q = 1) : d156674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25400, d156674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25400, d156674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62192 (p : Pattern) (ha : d25401 p = 1) (hb : d152855 p = 1) : d156561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25390 q = 1) (hb : d152855 q = 1) : d156553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25390, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25390, d156553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25401 q = 1) (hb : d152855 q = 1) : d156561 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25401, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25401, d156561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62193 (p : Pattern) (ha : d25407 p = 1) (hb : d152855 p = 1) : d156742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d152855 q = 1) : d156659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62188 q ha hb
    | true =>
      simp only [d25392, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62189 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d152855 q = 1) : d156731 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d152855 q = 1) : d156732 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d152855 q = 1) : d156733 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d152855 q = 1) : d156734 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25402 q = 1) (hb : d152855 q = 1) : d156675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25402, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62191 q ha hb
    | true =>
      simp only [d25402, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62192 q ha hb
  have h7 (q : Pattern) (ha : d25403 q = 1) (hb : d152855 q = 1) : d156738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25403, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25403, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25404 q = 1) (hb : d152855 q = 1) : d156739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25404, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25404, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25405 q = 1) (hb : d152855 q = 1) : d156740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25405, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25405, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25406 q = 1) (hb : d152855 q = 1) : d156741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25406, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25406, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25407 q = 1) (hb : d152855 q = 1) : d156742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25407, d156742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25407, d156742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62194 (p : Pattern) (ha : d25556 p = 1) (hb : d152855 p = 1) : d156809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25392 q = 1) (hb : d152855 q = 1) : d156659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25392, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62188 q ha hb
    | true =>
      simp only [d25392, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62189 q ha hb
  have h2 (q : Pattern) (ha : d25393 q = 1) (hb : d152855 q = 1) : d156731 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25393, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25393, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25394 q = 1) (hb : d152855 q = 1) : d156732 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25394, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25394, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25395 q = 1) (hb : d152855 q = 1) : d156733 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25395, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25395, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25396 q = 1) (hb : d152855 q = 1) : d156734 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25396, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25396, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25551 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62189 q ha hb
    | true =>
      simp only [d25551, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25552 q = 1) (hb : d152855 q = 1) : d156613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25553 q = 1) (hb : d152855 q = 1) : d156614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25553, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25554 q = 1) (hb : d152855 q = 1) : d156615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25555 q = 1) (hb : d152855 q = 1) : d156616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25556 q = 1) (hb : d152855 q = 1) : d156809 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25556, d156809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25556, d156809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62195 (p : Pattern) (ha : d25562 p = 1) (hb : d152855 p = 1) : d156624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25551 q = 1) (hb : d152855 q = 1) : d156555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25551, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62189 q ha hb
    | true =>
      simp only [d25551, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25552 q = 1) (hb : d152855 q = 1) : d156613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25552, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25552, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25553 q = 1) (hb : d152855 q = 1) : d156614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25553, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25553, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25554 q = 1) (hb : d152855 q = 1) : d156615 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25554, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25554, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25555 q = 1) (hb : d152855 q = 1) : d156616 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25555, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25555, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25557 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62192 q ha hb
    | true =>
      simp only [d25557, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25558 q = 1) (hb : d152855 q = 1) : d156620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25559 q = 1) (hb : d152855 q = 1) : d156621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25559, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25560 q = 1) (hb : d152855 q = 1) : d156622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25561 q = 1) (hb : d152855 q = 1) : d156623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25562 q = 1) (hb : d152855 q = 1) : d156624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25562, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25562, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62196 (p : Pattern) (ha : d25571 p = 1) (hb : d152855 p = 1) : d156818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25557 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25557, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62192 q ha hb
    | true =>
      simp only [d25557, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25558 q = 1) (hb : d152855 q = 1) : d156620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25558, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25558, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25559 q = 1) (hb : d152855 q = 1) : d156621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25559, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25559, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25560 q = 1) (hb : d152855 q = 1) : d156622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25560, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25560, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25561 q = 1) (hb : d152855 q = 1) : d156623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25561, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25561, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25571 q = 1) (hb : d152855 q = 1) : d156818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25571, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25571, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62197 (p : Pattern) (ha : d25614 p = 1) (hb : d152855 p = 1) : d156589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25154 q = 1) (hb : d152855 q = 1) : d156584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62157 q ha hb
    | true =>
      simp only [d25154, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
  have h2 (q : Pattern) (ha : d25155 q = 1) (hb : d152855 q = 1) : d156585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25156 q = 1) (hb : d152855 q = 1) : d156586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25604 q = 1) (hb : d152855 q = 1) : d156587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25604, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25613 q = 1) (hb : d152855 q = 1) : d156588 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25613, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25613, d156588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25614 q = 1) (hb : d152855 q = 1) : d156589 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25614, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25614, d156589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62198 (p : Pattern) (ha : d25670 p = 1) (hb : d152855 p = 1) : d156595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25615 q = 1) (hb : d152855 q = 1) : d156590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62197 q ha hb
    | true =>
      simp only [d25615, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25616 q = 1) (hb : d152855 q = 1) : d156591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25667 q = 1) (hb : d152855 q = 1) : d156592 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25667, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25667, d156592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25668 q = 1) (hb : d152855 q = 1) : d156593 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25668, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25668, d156593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25669 q = 1) (hb : d152855 q = 1) : d156594 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25669, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25669, d156594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25670 q = 1) (hb : d152855 q = 1) : d156595 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25670, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25670, d156595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62199 (p : Pattern) (ha : d25676 p = 1) (hb : d152855 p = 1) : d156859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25671 q = 1) (hb : d152855 q = 1) : d156596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25671, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62198 q ha hb
    | true =>
      simp only [d25671, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25672 q = 1) (hb : d152855 q = 1) : d156855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25672, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25672, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25673 q = 1) (hb : d152855 q = 1) : d156856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25673, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25673, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25674 q = 1) (hb : d152855 q = 1) : d156857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25674, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25674, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25675 q = 1) (hb : d152855 q = 1) : d156858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25675, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25675, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25676 q = 1) (hb : d152855 q = 1) : d156859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25676, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25676, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62200 (p : Pattern) (ha : d25412 p = 1) (hb : d152855 p = 1) : d156747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62186 q ha hb
    | true =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d152855 q = 1) : d156746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25412 q = 1) (hb : d152855 q = 1) : d156747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25412, d156747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25412, d156747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62201 (p : Pattern) (ha : d25414 p = 1) (hb : d152855 p = 1) : d156629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d152855 q = 1) : d156628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25414 q = 1) (hb : d152855 q = 1) : d156629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25414, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25414, d156629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62202 (p : Pattern) (ha : d25421 p = 1) (hb : d152855 p = 1) : d156754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62186 q ha hb
    | true =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d152855 q = 1) : d156752 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d152855 q = 1) : d156753 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25421 q = 1) (hb : d152855 q = 1) : d156754 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25421, d156754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25421, d156754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62203 (p : Pattern) (ha : d25424 p = 1) (hb : d152855 p = 1) : d156636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d152855 q = 1) : d156634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d152855 q = 1) : d156635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25424 q = 1) (hb : d152855 q = 1) : d156636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25424, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25424, d156636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62204 (p : Pattern) (ha : d25438 p = 1) (hb : d152854 p = 1) : d248584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25431 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25437 q = 1) (hb : d152852 q = 1) : d25437 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25438 q = 1) (hb : d152854 q = 1) : d248584 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25438, d152854, d248584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25438, d152854, d248584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62205 (p : Pattern) (ha : d25443 p = 1) (hb : d152854 p = 1) : d248589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25212 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25220 q = 1) (hb : d152852 q = 1) : d25220 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25443 q = 1) (hb : d152854 q = 1) : d248589 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25443, d152854, d248589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25443, d152854, d248589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62206 (p : Pattern) (ha : d25457 p = 1) (hb : d152855 p = 1) : d248595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25439 q = 1) (hb : d152854 q = 1) : d248585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d248585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62204 q ha hb
    | true =>
      simp only [d25439, d248585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25440 q = 1) (hb : d152854 q = 1) : d248586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d248586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25440, d248586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25441 q = 1) (hb : d152854 q = 1) : d248587 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25441, d248587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25441, d248587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25442 q = 1) (hb : d152854 q = 1) : d248588 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25442, d248588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25442, d248588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25444 q = 1) (hb : d152854 q = 1) : d248590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62205 q ha hb
    | true =>
      simp only [d25444, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25445 q = 1) (hb : d152854 q = 1) : d248591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25445, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25446 q = 1) (hb : d152854 q = 1) : d248592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25446, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25446, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25447 q = 1) (hb : d152854 q = 1) : d248593 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25447, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25447, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25448 q = 1) (hb : d152854 q = 1) : d248594 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25448, d248594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25448, d248594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25456 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25457 q = 1) (hb : d152855 q = 1) : d248595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25457, d152855, d248595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25457, d152855, d248595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62207 (p : Pattern) (ha : d25221 p = 1) (hb : d152854 p = 1) : d156536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25220 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23 q = 1) (hb : d152852 q = 1) : d23 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25221 q = 1) (hb : d152854 q = 1) : d156536 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25221, d152854, d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25221, d152854, d156536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62208 (p : Pattern) (ha : d25461 p = 1) (hb : d152855 p = 1) : d156542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25222 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62207 q ha hb
    | true =>
      simp only [d25222, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25223 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25223, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25224 q = 1) (hb : d152854 q = 1) : d156539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25224, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25224, d156539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25225 q = 1) (hb : d152854 q = 1) : d156540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25225, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25225, d156540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25226 q = 1) (hb : d152854 q = 1) : d156541 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25226, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25226, d156541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d29 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25461 q = 1) (hb : d152855 q = 1) : d156542 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25461, d152855, d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25461, d152855, d156542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62209 (p : Pattern) (ha : d25467 p = 1) (hb : d152855 p = 1) : d248601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25458 q = 1) (hb : d152855 q = 1) : d248596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25458, d248596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62206 q ha hb
    | true =>
      simp only [d25458, d248596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62168 q ha hb
  have h2 (q : Pattern) (ha : d25459 q = 1) (hb : d152855 q = 1) : d248597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25459, d248597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25459, d248597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25460 q = 1) (hb : d152855 q = 1) : d248598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25460, d248598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25460, d248598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25462 q = 1) (hb : d152855 q = 1) : d156647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25462, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62168 q ha hb
    | true =>
      simp only [d25462, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62208 q ha hb
  have h5 (q : Pattern) (ha : d25463 q = 1) (hb : d152855 q = 1) : d156648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25463, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25463, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25464 q = 1) (hb : d152855 q = 1) : d156649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25464, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25464, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25465 q = 1) (hb : d152855 q = 1) : d248599 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25465, d248599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25465, d248599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25228 q = 1) (hb : d152855 q = 1) : d156647 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25228, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62168 q ha hb
    | true =>
      simp only [d25228, d156647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62150 q ha hb
  have h9 (q : Pattern) (ha : d25229 q = 1) (hb : d152855 q = 1) : d156648 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25229, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25229, d156648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25230 q = 1) (hb : d152855 q = 1) : d156649 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25230, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25230, d156649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25111 q = 1) (hb : d152855 q = 1) : d156543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25111, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62150 q ha hb
    | true =>
      simp only [d25111, d156543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30049 q ha hb
  have h12 (q : Pattern) (ha : d25112 q = 1) (hb : d152855 q = 1) : d156544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25112, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25112, d156544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25113 q = 1) (hb : d152855 q = 1) : d156545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25113, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25113, d156545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25231 q = 1) (hb : d152855 q = 1) : d156650 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25231, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25231, d156650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25466 q = 1) (hb : d152855 q = 1) : d248600 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25466, d248600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25466, d248600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25467 q = 1) (hb : d152855 q = 1) : d248601 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25467, d248601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25467, d248601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62210 (p : Pattern) (ha : d25473 p = 1) (hb : d152855 p = 1) : d248607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d152855 q = 1) : d248602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d248602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62209 q ha hb
    | true =>
      simp only [d25468, d248602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d152855 q = 1) : d248603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d248603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d248603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62186 q ha hb
    | true =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d152855 q = 1) : d248604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d248604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d248604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d152855 q = 1) : d248605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d248605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d248605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d152855 q = 1) : d248606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d248606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d248606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25473 q = 1) (hb : d152855 q = 1) : d248607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25473, d248607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25473, d248607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62211 (p : Pattern) (ha : d25519 p = 1) (hb : d152855 p = 1) : d156782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62186 q ha hb
    | true =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d152855 q = 1) : d156779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d152855 q = 1) : d156780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d152855 q = 1) : d156781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25519 q = 1) (hb : d152855 q = 1) : d156782 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25519, d156782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25519, d156782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62212 (p : Pattern) (ha : d152855 p = 1) (hb : d202054 p = 1) : d248613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d152855 q = 1) : d156748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62200 q ha hb
    | true =>
      simp only [d25415, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62201 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d152855 q = 1) : d156749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d152855 q = 1) : d156750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d152855 q = 1) : d156751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d152855 q = 1) : d156755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62202 q ha hb
    | true =>
      simp only [d25425, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62203 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d152855 q = 1) : d156756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d152855 q = 1) : d156757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d152855 q = 1) : d248608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d248608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62210 q ha hb
    | true =>
      simp only [d25474, d248608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62188 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202050 q = 1) : d248609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d248609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202050, d248609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d152855 q = 1) : d156783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62211 q ha hb
    | true =>
      simp only [d25520, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d152855 q = 1) : d156784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202051 q = 1) : d248610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d248610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d248610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202052 q = 1) : d248611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d248611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202052, d248611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202053 q = 1) : d248612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d248612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202053, d248612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202054 q = 1) : d248613 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202054, d248613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202054, d248613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro62213 (p : Pattern) (ha : d25526 p = 1) (hb : d152855 p = 1) : d156789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62186 q ha hb
    | true =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25385 q = 1) (hb : d152855 q = 1) : d156656 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25385, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25385, d156656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25411 q = 1) (hb : d152855 q = 1) : d156746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25411, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25411, d156746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25526 q = 1) (hb : d152855 q = 1) : d156789 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25526, d156789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25526, d156789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62214 (p : Pattern) (ha : d25527 p = 1) (hb : d152855 p = 1) : d156665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25389 q = 1) (hb : d152855 q = 1) : d156552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25389, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25389, d156552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25413 q = 1) (hb : d152855 q = 1) : d156628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25413, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25413, d156628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25527 q = 1) (hb : d152855 q = 1) : d156665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25527, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25527, d156665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62215 (p : Pattern) (ha : d25532 p = 1) (hb : d152855 p = 1) : d156794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62186 q ha hb
    | true =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d152855 q = 1) : d156655 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d156655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d152855 q = 1) : d156752 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d156752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d152855 q = 1) : d156753 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d156753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25532 q = 1) (hb : d152855 q = 1) : d156794 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25532, d156794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25532, d156794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62216 (p : Pattern) (ha : d25533 p = 1) (hb : d152855 p = 1) : d156670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d152855 q = 1) : d156549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62187 q ha hb
    | true =>
      simp only [d25382, d156549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d152855 q = 1) : d156550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d156550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d152855 q = 1) : d156551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d156551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d152855 q = 1) : d156634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d156634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d152855 q = 1) : d156635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d156635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25533 q = 1) (hb : d152855 q = 1) : d156670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25533, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25533, d156670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62217 (p : Pattern) (ha : d25537 p = 1) (hb : d152855 p = 1) : d248614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d152855 q = 1) : d248602 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d248602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62209 q ha hb
    | true =>
      simp only [d25468, d248602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d152855 q = 1) : d248603 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d248603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d248603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62186 q ha hb
    | true =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d152855 q = 1) : d248604 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d248604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d248604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d152855 q = 1) : d248605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d248605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d248605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d152855 q = 1) : d248606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d248606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d248606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25537 q = 1) (hb : d152855 q = 1) : d248614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25537, d248614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25537, d248614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62218 (p : Pattern) (ha : d25543 p = 1) (hb : d152855 p = 1) : d156801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d152855 q = 1) : d156653 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62186 q ha hb
    | true =>
      simp only [d25378, d156653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d152855 q = 1) : d156654 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d156654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d152855 q = 1) : d156779 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d156779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d152855 q = 1) : d156780 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d156780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d152855 q = 1) : d156781 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d156781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25543 q = 1) (hb : d152855 q = 1) : d156801 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25543, d156801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25543, d156801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62219 (p : Pattern) (ha : d152855 p = 1) (hb : d202059 p = 1) : d248620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d152855 q = 1) : d156748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62200 q ha hb
    | true =>
      simp only [d25415, d156748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62201 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d152855 q = 1) : d156749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d156749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d152855 q = 1) : d156750 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d156750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d152855 q = 1) : d156751 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d156751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d152855 q = 1) : d156755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62202 q ha hb
    | true =>
      simp only [d25425, d156755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62203 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d152855 q = 1) : d156756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d156756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d152855 q = 1) : d156757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d156757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d152855 q = 1) : d248608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d248608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62210 q ha hb
    | true =>
      simp only [d25474, d248608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62188 q ha hb
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202050 q = 1) : d248609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d248609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d202050, d248609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d152855 q = 1) : d156783 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62211 q ha hb
    | true =>
      simp only [d25520, d156783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d152855 q = 1) : d156784 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d156784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d152855 q = 1) (hb : d202051 q = 1) : d248610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d248610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d248610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202052 q = 1) : d248611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d248611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d202052, d248611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202053 q = 1) : d248612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d248612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d202053, d248612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25528 q = 1) (hb : d152855 q = 1) : d156790 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25528, d156790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62213 q ha hb
    | true =>
      simp only [d25528, d156790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62214 q ha hb
  have h16 (q : Pattern) (ha : d25529 q = 1) (hb : d152855 q = 1) : d156791 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25529, d156791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25529, d156791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25530 q = 1) (hb : d152855 q = 1) : d156792 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25530, d156792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25530, d156792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25531 q = 1) (hb : d152855 q = 1) : d156793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25531, d156793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25531, d156793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25534 q = 1) (hb : d152855 q = 1) : d156795 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25534, d156795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62215 q ha hb
    | true =>
      simp only [d25534, d156795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62216 q ha hb
  have h20 (q : Pattern) (ha : d25535 q = 1) (hb : d152855 q = 1) : d156796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25535, d156796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25535, d156796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25536 q = 1) (hb : d152855 q = 1) : d156797 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25536, d156797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25536, d156797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25538 q = 1) (hb : d152855 q = 1) : d248615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d248615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62217 q ha hb
    | true =>
      simp only [d25538, d248615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62191 q ha hb
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202055 q = 1) : d248616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d248616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d202055, d248616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d25544 q = 1) (hb : d152855 q = 1) : d156802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62218 q ha hb
    | true =>
      simp only [d25544, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25545 q = 1) (hb : d152855 q = 1) : d156803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25545, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d152855 q = 1) (hb : d202056 q = 1) : d248617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d248617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202056, d248617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d152855 q = 1) (hb : d202057 q = 1) : d248618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202057, d248618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d202057, d248618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d152855 q = 1) (hb : d202058 q = 1) : d248619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202058, d248619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d202058, d248619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d152855 q = 1) (hb : d202059 q = 1) : d248620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202059, d248620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202059, d248620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro62220 (p : Pattern) (ha : d152855 p = 1) (hb : d202066 p = 1) : d248627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25538 q = 1) (hb : d152855 q = 1) : d248615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d248615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62217 q ha hb
    | true =>
      simp only [d25538, d248615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62191 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202055 q = 1) : d248616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d248616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202055, d248616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d25544 q = 1) (hb : d152855 q = 1) : d156802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62218 q ha hb
    | true =>
      simp only [d25544, d156802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25545 q = 1) (hb : d152855 q = 1) : d156803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25545, d156803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202056 q = 1) : d248617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d248617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202056, d248617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202064 q = 1) : d248625 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202064, d248625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202064, d248625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202065 q = 1) : d248626 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202065, d248626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202065, d248626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202066 q = 1) : d248627 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202066, d248627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202066, d248627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62221 (p : Pattern) (ha : d25591 p = 1) (hb : d152855 p = 1) : d248642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25577 q = 1) (hb : d152854 q = 1) : d248633 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25577, d248633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25577, d248633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62204 q ha hb
  have h2 (q : Pattern) (ha : d25439 q = 1) (hb : d152854 q = 1) : d248585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d248585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62204 q ha hb
    | true =>
      simp only [d25439, d248585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25578 q = 1) (hb : d152854 q = 1) : d248634 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25578, d248634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25578, d248634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25440 q = 1) (hb : d152854 q = 1) : d248586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d248586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25440, d248586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25579 q = 1) (hb : d152854 q = 1) : d248635 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25579, d248635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25579, d248635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25580 q = 1) (hb : d152854 q = 1) : d248636 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25580, d248636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25580, d248636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25581 q = 1) (hb : d152854 q = 1) : d248637 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25581, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25581, d248637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62205 q ha hb
  have h8 (q : Pattern) (ha : d25444 q = 1) (hb : d152854 q = 1) : d248590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62205 q ha hb
    | true =>
      simp only [d25444, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25582 q = 1) (hb : d152854 q = 1) : d248638 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25582, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25582, d248638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25445 q = 1) (hb : d152854 q = 1) : d248591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25445, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25583 q = 1) (hb : d152854 q = 1) : d248639 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25583, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25583, d248639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25584 q = 1) (hb : d152854 q = 1) : d248640 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25584, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25584, d248640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25585 q = 1) (hb : d152854 q = 1) : d248641 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25585, d248641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25585, d248641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25590 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25591 q = 1) (hb : d152855 q = 1) : d248642 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25591, d152855, d248642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25591, d152855, d248642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62222 (p : Pattern) (ha : d25595 p = 1) (hb : d152855 p = 1) : d156583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25314 q = 1) (hb : d152854 q = 1) : d156578 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25314, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25314, d156578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62207 q ha hb
  have h2 (q : Pattern) (ha : d25222 q = 1) (hb : d152854 q = 1) : d156537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25222, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62207 q ha hb
    | true =>
      simp only [d25222, d156537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25315 q = 1) (hb : d152854 q = 1) : d156579 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25315, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25315, d156579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25223 q = 1) (hb : d152854 q = 1) : d156538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25223, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25223, d156538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25316 q = 1) (hb : d152854 q = 1) : d156580 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25316, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25316, d156580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25317 q = 1) (hb : d152854 q = 1) : d156581 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25317, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25317, d156581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30048 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25318 q = 1) (hb : d152854 q = 1) : d156582 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25318, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25318, d156582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d70 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25595 q = 1) (hb : d152855 q = 1) : d156583 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25595, d152855, d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25595, d152855, d156583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62223 (p : Pattern) (ha : d25601 p = 1) (hb : d152855 p = 1) : d248648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25592 q = 1) (hb : d152855 q = 1) : d248643 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25592, d248643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62221 q ha hb
    | true =>
      simp only [d25592, d248643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62179 q ha hb
  have h2 (q : Pattern) (ha : d25593 q = 1) (hb : d152855 q = 1) : d248644 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25593, d248644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25593, d248644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25594 q = 1) (hb : d152855 q = 1) : d248645 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25594, d248645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25594, d248645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25596 q = 1) (hb : d152855 q = 1) : d156701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25596, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62179 q ha hb
    | true =>
      simp only [d25596, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62222 q ha hb
  have h5 (q : Pattern) (ha : d25597 q = 1) (hb : d152855 q = 1) : d156702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25597, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25597, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25598 q = 1) (hb : d152855 q = 1) : d156703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25598, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25598, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25599 q = 1) (hb : d152855 q = 1) : d248646 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25599, d248646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25599, d248646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25320 q = 1) (hb : d152855 q = 1) : d156701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62179 q ha hb
    | true =>
      simp only [d25320, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62157 q ha hb
  have h9 (q : Pattern) (ha : d25321 q = 1) (hb : d152855 q = 1) : d156702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25322 q = 1) (hb : d152855 q = 1) : d156703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25154 q = 1) (hb : d152855 q = 1) : d156584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62157 q ha hb
    | true =>
      simp only [d25154, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
  have h12 (q : Pattern) (ha : d25155 q = 1) (hb : d152855 q = 1) : d156585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25156 q = 1) (hb : d152855 q = 1) : d156586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25323 q = 1) (hb : d152855 q = 1) : d156704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25323, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25600 q = 1) (hb : d152855 q = 1) : d248647 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25600, d248647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25600, d248647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25601 q = 1) (hb : d152855 q = 1) : d248648 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25601, d248648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25601, d248648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro62224 (p : Pattern) (ha : d25606 p = 1) (hb : d152855 p = 1) : d156706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25320 q = 1) (hb : d152855 q = 1) : d156701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62179 q ha hb
    | true =>
      simp only [d25320, d156701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62157 q ha hb
  have h2 (q : Pattern) (ha : d25321 q = 1) (hb : d152855 q = 1) : d156702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d156702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25322 q = 1) (hb : d152855 q = 1) : d156703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d156703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25154 q = 1) (hb : d152855 q = 1) : d156584 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62157 q ha hb
    | true =>
      simp only [d25154, d156584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30056 q ha hb
  have h5 (q : Pattern) (ha : d25155 q = 1) (hb : d152855 q = 1) : d156585 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d156585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25156 q = 1) (hb : d152855 q = 1) : d156586 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d156586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25323 q = 1) (hb : d152855 q = 1) : d156704 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25323, d156704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25604 q = 1) (hb : d152855 q = 1) : d156587 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25604, d156587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25605 q = 1) (hb : d152855 q = 1) : d156705 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25605, d156705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25605, d156705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25606 q = 1) (hb : d152855 q = 1) : d156706 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25606, d156706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25606, d156706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62225 (p : Pattern) (ha : d25612 p = 1) (hb : d152855 p = 1) : d248654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25602 q = 1) (hb : d152855 q = 1) : d248649 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25602, d248649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62223 q ha hb
    | true =>
      simp only [d25602, d248649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25603 q = 1) (hb : d152855 q = 1) : d248650 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25603, d248650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25603, d248650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25607 q = 1) (hb : d152855 q = 1) : d156707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62224 q ha hb
    | true =>
      simp only [d25607, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25608 q = 1) (hb : d152855 q = 1) : d156708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25609 q = 1) (hb : d152855 q = 1) : d248651 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25609, d248651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25609, d248651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25610 q = 1) (hb : d152855 q = 1) : d248652 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25610, d248652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25610, d248652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25611 q = 1) (hb : d152855 q = 1) : d248653 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25611, d248653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25611, d248653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25612 q = 1) (hb : d152855 q = 1) : d248654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25612, d248654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25612, d248654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62226 (p : Pattern) (ha : d25620 p = 1) (hb : d152855 p = 1) : d156712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25607 q = 1) (hb : d152855 q = 1) : d156707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62224 q ha hb
    | true =>
      simp only [d25607, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25608 q = 1) (hb : d152855 q = 1) : d156708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25615 q = 1) (hb : d152855 q = 1) : d156590 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62197 q ha hb
    | true =>
      simp only [d25615, d156590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25616 q = 1) (hb : d152855 q = 1) : d156591 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d156591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25617 q = 1) (hb : d152855 q = 1) : d156709 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25617, d156709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25617, d156709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25618 q = 1) (hb : d152855 q = 1) : d156710 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25618, d156710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25618, d156710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25619 q = 1) (hb : d152855 q = 1) : d156711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25619, d156711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25619, d156711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25620 q = 1) (hb : d152855 q = 1) : d156712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25620, d156712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25620, d156712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62227 (p : Pattern) (ha : d25659 p = 1) (hb : d152855 p = 1) : d156847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25607 q = 1) (hb : d152855 q = 1) : d156707 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62224 q ha hb
    | true =>
      simp only [d25607, d156707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25608 q = 1) (hb : d152855 q = 1) : d156708 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d156708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25656 q = 1) (hb : d152855 q = 1) : d156844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25656, d156844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25656, d156844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25657 q = 1) (hb : d152855 q = 1) : d156845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25657, d156845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25657, d156845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25658 q = 1) (hb : d152855 q = 1) : d156846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25658, d156846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25658, d156846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25659 q = 1) (hb : d152855 q = 1) : d156847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25659, d156847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25659, d156847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62228 (p : Pattern) (ha : d152855 p = 1) (hb : d202076 p = 1) : d248660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25621 q = 1) (hb : d152855 q = 1) : d248655 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25621, d248655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62225 q ha hb
    | true =>
      simp only [d25621, d248655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62226 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202072 q = 1) : d248656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202072, d248656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d202072, d248656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d25660 q = 1) (hb : d152855 q = 1) : d156848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25660, d156848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62227 q ha hb
    | true =>
      simp only [d25660, d156848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25661 q = 1) (hb : d152855 q = 1) : d156849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25661, d156849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25661, d156849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202073 q = 1) : d248657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202073, d248657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202073, d248657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202074 q = 1) : d248658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202074, d248658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202074, d248658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d152855 q = 1) (hb : d202075 q = 1) : d248659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202075, d248659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202075, d248659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202076 q = 1) : d248660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202076, d248660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202076, d248660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62229 (p : Pattern) (ha : d152855 p = 1) (hb : d202082 p = 1) : d248666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25398 q = 1) (hb : d152855 q = 1) : d156736 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25398, d156736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25398, d156736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62190 q ha hb
  have h2 (q : Pattern) (ha : d25399 q = 1) (hb : d152855 q = 1) : d156737 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25399, d156737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25399, d156737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25408 q = 1) (hb : d152855 q = 1) : d156743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25408, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62190 q ha hb
    | true =>
      simp only [d25408, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62193 q ha hb
  have h4 (q : Pattern) (ha : d25409 q = 1) (hb : d152855 q = 1) : d156744 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25409, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25409, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25410 q = 1) (hb : d152855 q = 1) : d156745 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25410, d156745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25410, d156745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202060 q = 1) : d248621 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202060, d248621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62212 q ha hb
    | true =>
      simp only [d202060, d248621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62219 q ha hb
  have h7 (q : Pattern) (ha : d25563 q = 1) (hb : d152855 q = 1) : d156810 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25563, d156810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62194 q ha hb
    | true =>
      simp only [d25563, d156810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62195 q ha hb
  have h8 (q : Pattern) (ha : d152855 q = 1) (hb : d202061 q = 1) : d248622 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202061, d248622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202061, d248622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d152855 q = 1) (hb : d202062 q = 1) : d248623 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202062, d248623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202062, d248623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d152855 q = 1) (hb : d202063 q = 1) : d248624 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202063, d248624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d202063, d248624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d152855 q = 1) (hb : d202067 q = 1) : d248628 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202067, d248628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202067, d248628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62220 q ha hb
  have h12 (q : Pattern) (ha : d25572 q = 1) (hb : d152855 q = 1) : d156819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25572, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25572, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62196 q ha hb
  have h13 (q : Pattern) (ha : d152855 q = 1) (hb : d202068 q = 1) : d248629 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202068, d248629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202068, d248629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d152855 q = 1) (hb : d202069 q = 1) : d248630 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202069, d248630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202069, d248630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d152855 q = 1) (hb : d202070 q = 1) : d248631 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202070, d248631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202070, d248631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d152855 q = 1) (hb : d202071 q = 1) : d248632 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202071, d248632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202071, d248632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d152855 q = 1) (hb : d202077 q = 1) : d248661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202077, d248661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202077, d248661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62228 q ha hb
  have h18 (q : Pattern) (ha : d25677 q = 1) (hb : d152855 q = 1) : d156860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25677, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25677, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62199 q ha hb
  have h19 (q : Pattern) (ha : d152855 q = 1) (hb : d202078 q = 1) : d248662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202078, d248662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202078, d248662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d152855 q = 1) (hb : d202079 q = 1) : d248663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202079, d248663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202079, d248663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d152855 q = 1) (hb : d202080 q = 1) : d248664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202080, d248664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202080, d248664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d152855 q = 1) (hb : d202081 q = 1) : d248665 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202081, d248665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202081, d248665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d152855 q = 1) (hb : d202082 q = 1) : d248666 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202082, d248666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202082, d248666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro62230 (p : Pattern) (ha : d152855 p = 1) (hb : d202088 p = 1) : d248672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d152855 q = 1) (hb : d202083 q = 1) : d248667 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202083, d248667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202083, d248667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62229 q ha hb
  have h2 (q : Pattern) (ha : d152855 q = 1) (hb : d202084 q = 1) : d248668 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202084, d248668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202084, d248668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d152855 q = 1) (hb : d202085 q = 1) : d248669 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202085, d248669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202085, d248669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d152855 q = 1) (hb : d202086 q = 1) : d248670 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202086, d248670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202086, d248670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d152855 q = 1) (hb : d202087 q = 1) : d248671 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202087, d248671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202087, d248671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d152855 q = 1) (hb : d202088 q = 1) : d248672 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202088, d248672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d202088, d248672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62231 (p : Pattern) (ha : d25696 p = 1) (hb : d152855 p = 1) : d248595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25439 q = 1) (hb : d152854 q = 1) : d248585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d248585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62204 q ha hb
    | true =>
      simp only [d25439, d248585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25440 q = 1) (hb : d152854 q = 1) : d248586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d248586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25440, d248586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25441 q = 1) (hb : d152854 q = 1) : d248587 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25441, d248587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25441, d248587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25442 q = 1) (hb : d152854 q = 1) : d248588 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25442, d248588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25442, d248588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25444 q = 1) (hb : d152854 q = 1) : d248590 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62205 q ha hb
    | true =>
      simp only [d25444, d248590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25445 q = 1) (hb : d152854 q = 1) : d248591 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25445, d248591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25446 q = 1) (hb : d152854 q = 1) : d248592 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25446, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25446, d248592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25447 q = 1) (hb : d152854 q = 1) : d248593 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25447, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25447, d248593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25448 q = 1) (hb : d152854 q = 1) : d248594 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25448, d248594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25448, d248594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25695 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25696 q = 1) (hb : d152855 q = 1) : d248595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25696, d152855, d248595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25696, d152855, d248595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62232 (p : Pattern) (ha : d25690 p = 1) (hb : d152854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d25103 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152852 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25690 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25690, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d25690, d152854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro62233 (p : Pattern) (ha : d25699 p = 1) (hb : d152855 p = 1) : d156874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25214 q = 1) (hb : d152854 q = 1) : d156641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62167 q ha hb
    | true =>
      simp only [d25214, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25215 q = 1) (hb : d152854 q = 1) : d156642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25215, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25216 q = 1) (hb : d152854 q = 1) : d156643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25216, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25216, d156643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25217 q = 1) (hb : d152854 q = 1) : d156644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25217, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25217, d156644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25691 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62232 q ha hb
    | true =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25692 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25693 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25694 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25697 q = 1) (hb : d152854 q = 1) : d156873 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25697, d156873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25697, d156873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d25698 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25699 q = 1) (hb : d152855 q = 1) : d156874 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25699, d152855, d156874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25699, d152855, d156874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro62234 (p : Pattern) (ha : d25703 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25691 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62232 q ha hb
    | true =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25692 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25693 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25694 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25698 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25703 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25703, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25703, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro62235 (p : Pattern) (ha : d25710 p = 1) (hb : d152855 p = 1) : d248679 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25700 q = 1) (hb : d152855 q = 1) : d248674 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25700, d248674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62231 q ha hb
    | true =>
      simp only [d25700, d248674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62233 q ha hb
  have h2 (q : Pattern) (ha : d25701 q = 1) (hb : d152855 q = 1) : d248675 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25701, d248675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25701, d248675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25702 q = 1) (hb : d152855 q = 1) : d248676 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25702, d248676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25702, d248676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25704 q = 1) (hb : d152855 q = 1) : d156878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62233 q ha hb
    | true =>
      simp only [d25704, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62234 q ha hb
  have h5 (q : Pattern) (ha : d25705 q = 1) (hb : d152855 q = 1) : d156879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25706 q = 1) (hb : d152855 q = 1) : d156880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25707 q = 1) (hb : d152855 q = 1) : d248677 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25707, d248677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25707, d248677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25708 q = 1) (hb : d152855 q = 1) : d156882 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25708, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25708, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25709 q = 1) (hb : d152855 q = 1) : d248678 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25709, d248678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25709, d248678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25710 q = 1) (hb : d152855 q = 1) : d248679 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25710, d248679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25710, d248679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro62236 (p : Pattern) (ha : d25714 p = 1) (hb : d152855 p = 1) : d156888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25704 q = 1) (hb : d152855 q = 1) : d156878 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62233 q ha hb
    | true =>
      simp only [d25704, d156878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62234 q ha hb
  have h2 (q : Pattern) (ha : d25705 q = 1) (hb : d152855 q = 1) : d156879 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d156879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25706 q = 1) (hb : d152855 q = 1) : d156880 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d156880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25708 q = 1) (hb : d152855 q = 1) : d156882 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25708, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25708, d156882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25713 q = 1) (hb : d152855 q = 1) : d156887 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25713, d156887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25713, d156887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25714 q = 1) (hb : d152855 q = 1) : d156888 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25714, d156888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25714, d156888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62237 (p : Pattern) (ha : d25720 p = 1) (hb : d152855 p = 1) : d248685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d152855 q = 1) : d248680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62235 q ha hb
    | true =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d152855 q = 1) : d248681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d152855 q = 1) : d248682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d152855 q = 1) : d248683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d248683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d248683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25719 q = 1) (hb : d152855 q = 1) : d248684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25719, d248684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25719, d248684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25720 q = 1) (hb : d152855 q = 1) : d248685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25720, d248685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25720, d248685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro62238 (p : Pattern) (ha : d25724 p = 1) (hb : d152855 p = 1) : d156898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d152855 q = 1) : d156896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25723 q = 1) (hb : d152855 q = 1) : d156897 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25723, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25723, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25724 q = 1) (hb : d152855 q = 1) : d156898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25724, d156898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25724, d156898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62239 (p : Pattern) (ha : d25730 p = 1) (hb : d152855 p = 1) : d248691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d152855 q = 1) : d248686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d248686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62237 q ha hb
    | true =>
      simp only [d25725, d248686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62238 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d152855 q = 1) : d248687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d248687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d248687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d152855 q = 1) : d248688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d248688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d248688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d152855 q = 1) : d248689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d248689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d248689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d152855 q = 1) : d248690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d248690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d248690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25730 q = 1) (hb : d152855 q = 1) : d248691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25730, d248691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25730, d248691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62240 (p : Pattern) (ha : d25733 p = 1) (hb : d152855 p = 1) : d248694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d152855 q = 1) : d248680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62235 q ha hb
    | true =>
      simp only [d25711, d248680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d152855 q = 1) : d248681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d248681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d152855 q = 1) : d248682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d248682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d152855 q = 1) : d248683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d248683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d248683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25719 q = 1) (hb : d152855 q = 1) : d248684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25719, d248684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25719, d248684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25733 q = 1) (hb : d152855 q = 1) : d248694 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25733, d248694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25733, d248694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro62241 (p : Pattern) (ha : d25734 p = 1) (hb : d152855 p = 1) : d156908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d152855 q = 1) : d156889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62236 q ha hb
    | true =>
      simp only [d25715, d156889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d152855 q = 1) : d156890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d156890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d152855 q = 1) : d156895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d156895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d152855 q = 1) : d156896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d156896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25723 q = 1) (hb : d152855 q = 1) : d156897 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25723, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25723, d156897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25734 q = 1) (hb : d152855 q = 1) : d156908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25734, d156908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25734, d156908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62242 (p : Pattern) (ha : d25740 p = 1) (hb : d152855 p = 1) : d248700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d152855 q = 1) : d248686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d248686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62237 q ha hb
    | true =>
      simp only [d25725, d248686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62238 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d152855 q = 1) : d248687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d248687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d248687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d152855 q = 1) : d248688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d248688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d248688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d152855 q = 1) : d248689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d248689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d248689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d152855 q = 1) : d248690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d248690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d248690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25735 q = 1) (hb : d152855 q = 1) : d248695 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25735, d248695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62240 q ha hb
    | true =>
      simp only [d25735, d248695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62241 q ha hb
  have h7 (q : Pattern) (ha : d25736 q = 1) (hb : d152855 q = 1) : d248696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25736, d248696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25736, d248696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25737 q = 1) (hb : d152855 q = 1) : d248697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25737, d248697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25737, d248697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25738 q = 1) (hb : d152855 q = 1) : d248698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25738, d248698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25738, d248698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25739 q = 1) (hb : d152855 q = 1) : d248699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25739, d248699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25739, d248699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25740 q = 1) (hb : d152855 q = 1) : d248700 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25740, d248700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25740, d248700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62243 (p : Pattern) (ha : d25912 p = 1) (hb : d152855 p = 1) : d248777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d152855 q = 1) : d248686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d248686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62237 q ha hb
    | true =>
      simp only [d25725, d248686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62238 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d152855 q = 1) : d248687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d248687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d248687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d152855 q = 1) : d248688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d248688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d248688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d152855 q = 1) : d248689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d248689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d248689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d152855 q = 1) : d248690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d248690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d248690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25907 q = 1) (hb : d152855 q = 1) : d157000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25907, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62238 q ha hb
    | true =>
      simp only [d25907, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25908 q = 1) (hb : d152855 q = 1) : d157001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25908, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25908, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25909 q = 1) (hb : d152855 q = 1) : d157002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25909, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25909, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25910 q = 1) (hb : d152855 q = 1) : d157003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25910, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25910, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25911 q = 1) (hb : d152855 q = 1) : d157004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25911, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25911, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25912 q = 1) (hb : d152855 q = 1) : d248777 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25912, d248777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25912, d248777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62244 (p : Pattern) (ha : d25918 p = 1) (hb : d152855 p = 1) : d157011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25907 q = 1) (hb : d152855 q = 1) : d157000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25907, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62238 q ha hb
    | true =>
      simp only [d25907, d157000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25908 q = 1) (hb : d152855 q = 1) : d157001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25908, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25908, d157001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25909 q = 1) (hb : d152855 q = 1) : d157002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25909, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25909, d157002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25910 q = 1) (hb : d152855 q = 1) : d157003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25910, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25910, d157003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25911 q = 1) (hb : d152855 q = 1) : d157004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25911, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25911, d157004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25913 q = 1) (hb : d152855 q = 1) : d157006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25913, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62241 q ha hb
    | true =>
      simp only [d25913, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25914 q = 1) (hb : d152855 q = 1) : d157007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25914, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25914, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25915 q = 1) (hb : d152855 q = 1) : d157008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25915, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25915, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25916 q = 1) (hb : d152855 q = 1) : d157009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25916, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25916, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25917 q = 1) (hb : d152855 q = 1) : d157010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25917, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25917, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25918 q = 1) (hb : d152855 q = 1) : d157011 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25918, d157011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25918, d157011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro62245 (p : Pattern) (ha : d25927 p = 1) (hb : d152855 p = 1) : d157020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25913 q = 1) (hb : d152855 q = 1) : d157006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25913, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62241 q ha hb
    | true =>
      simp only [d25913, d157006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25914 q = 1) (hb : d152855 q = 1) : d157007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25914, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25914, d157007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25915 q = 1) (hb : d152855 q = 1) : d157008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25915, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25915, d157008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25916 q = 1) (hb : d152855 q = 1) : d157009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25916, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25916, d157009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25917 q = 1) (hb : d152855 q = 1) : d157010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25917, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25917, d157010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25927 q = 1) (hb : d152855 q = 1) : d157020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25927, d157020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25927, d157020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro62246 (p : Pattern) (ha : d25964 p = 1) (hb : d152855 p = 1) : d157046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25309 q = 1) (hb : d152854 q = 1) : d156695 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25309, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25309, d156695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62167 q ha hb
  have h2 (q : Pattern) (ha : d25214 q = 1) (hb : d152854 q = 1) : d156641 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62167 q ha hb
    | true =>
      simp only [d25214, d156641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25310 q = 1) (hb : d152854 q = 1) : d156696 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25310, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25310, d156696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25215 q = 1) (hb : d152854 q = 1) : d156642 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25215, d156642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25311 q = 1) (hb : d152854 q = 1) : d156697 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25311, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25311, d156697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25312 q = 1) (hb : d152854 q = 1) : d156698 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25312, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25312, d156698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25948 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62232 q ha hb
  have h8 (q : Pattern) (ha : d25691 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62232 q ha hb
    | true =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25949 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25692 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25950 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25951 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25963 q = 1) (hb : d152854 q = 1) : d157045 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25963, d157045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25963, d157045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d25957 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25964 q = 1) (hb : d152855 q = 1) : d157046 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25964, d152855, d157046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25964, d152855, d157046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro62247 (p : Pattern) (ha : d25968 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25948 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62232 q ha hb
  have h2 (q : Pattern) (ha : d25691 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62232 q ha hb
    | true =>
      simp only [d25691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25949 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25692 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25950 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25951 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25957 q = 1) (hb : d152854 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d25968 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25968, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25968, d152855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro62248 (p : Pattern) (ha : d25987 p = 1) (hb : d152855 p = 1) : d157068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25969 q = 1) (hb : d152855 q = 1) : d157050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25969, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62246 q ha hb
    | true =>
      simp only [d25969, d157050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62247 q ha hb
  have h2 (q : Pattern) (ha : d25970 q = 1) (hb : d152855 q = 1) : d157051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25970, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25970, d157051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25971 q = 1) (hb : d152855 q = 1) : d157052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25971, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25971, d157052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25977 q = 1) (hb : d152855 q = 1) : d157058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25977, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25977, d157058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25986 q = 1) (hb : d152855 q = 1) : d157067 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25986, d157067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25986, d157067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25987 q = 1) (hb : d152855 q = 1) : d157068 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25987, d157068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25987, d157068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro62249 (p : Pattern) (ha : d26058 p = 1) (hb : d152855 p = 1) : d157091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25988 q = 1) (hb : d152855 q = 1) : d157069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25988, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62248 q ha hb
    | true =>
      simp only [d25988, d157069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25989 q = 1) (hb : d152855 q = 1) : d157070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25989, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25989, d157070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26055 q = 1) (hb : d152855 q = 1) : d157088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26055, d157088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26055, d157088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26056 q = 1) (hb : d152855 q = 1) : d157089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26056, d157089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26056, d157089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26057 q = 1) (hb : d152855 q = 1) : d157090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26057, d157090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26057, d157090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26058 q = 1) (hb : d152855 q = 1) : d157091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26058, d157091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26058, d157091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
