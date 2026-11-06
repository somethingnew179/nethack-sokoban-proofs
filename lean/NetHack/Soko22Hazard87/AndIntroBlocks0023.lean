import NetHack.Soko22Hazard87.AndIntroBlocks0022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro5750 (p : Pattern) (ha : d2563 p = 1) (hb : d52563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d52462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d52462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d52463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, d52463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d52464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d52464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d52465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d52465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2563 q = 1) (hb : d52563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, d52563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2563, d52563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5751 (p : Pattern) (ha : d3556 p = 1) (hb : d52569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52568 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3556 q = 1) (hb : d52569 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3556, d52569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3556, d52569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5752 (p : Pattern) (ha : d52556 p = 1) (hb : d62593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d52484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro134 q ha hb
    | true =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d52485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d52486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d52487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro136 q ha hb
    | true =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d852 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4446 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4446, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d909 q = 1) (hb : d52531 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d910 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4447 q = 1) (hb : d52533 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d52533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4447, d52533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51709 q = 1) (hb : d52534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51709, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51710 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51710, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52555 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52556 q = 1) (hb : d62593 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52556, d62593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d52556, d62593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro5753 (p : Pattern) (ha : d54663 p = 1) (hb : d62599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52466 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5749 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3553 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3553, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3553, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52536 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52557 q = 1) (hb : d62594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52557, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52557, d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5752 q ha hb
  have h8 (q : Pattern) (ha : d3557 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3557, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5750 q ha hb
    | true =>
      simp only [d3557, d52570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5751 q ha hb
  have h9 (q : Pattern) (ha : d52571 q = 1) (hb : d62595 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52571, d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52571, d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52572 q = 1) (hb : d62596 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52572, d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52573 q = 1) (hb : d62597 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d62597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52573, d62597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54662 q = 1) (hb : d62598 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54662, d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54662, d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d54663 q = 1) (hb : d62599 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54663, d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54663, d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h13 p ha hb
theorem andIntro5754 (p : Pattern) (ha : d54669 p = 1) (hb : d62605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54664 q = 1) (hb : d62600 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54664, d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54664, d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5753 q ha hb
  have h2 (q : Pattern) (ha : d54665 q = 1) (hb : d62601 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54665, d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54665, d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54666 q = 1) (hb : d62602 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54666, d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54666, d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54667 q = 1) (hb : d62603 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54667, d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54667, d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54668 q = 1) (hb : d62604 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54668, d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54668, d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54669 q = 1) (hb : d62605 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54669, d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54669, d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5755 (p : Pattern) (ha : d2578 p = 1) (hb : d52759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52758 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2578 q = 1) (hb : d52759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, d52759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2578, d52759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5756 (p : Pattern) (ha : d2578 p = 1) (hb : d52843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d52745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d52745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d52746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d52746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d52747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d52747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d52748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d52748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2578 q = 1) (hb : d52843 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, d52843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2578, d52843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5757 (p : Pattern) (ha : d3574 p = 1) (hb : d52849 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52848 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3574 q = 1) (hb : d52849 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3574, d52849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3574, d52849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5758 (p : Pattern) (ha : d52836 p = 1) (hb : d62608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d52767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro186 q ha hb
    | true =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d52768 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d52769 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro188 q ha hb
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4485 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1320 q = 1) (hb : d52811 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1321 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4486 q = 1) (hb : d52813 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d52813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4486, d52813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51736 q = 1) (hb : d52814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51736, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51737 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51737, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d52835 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d52836 q = 1) (hb : d62608 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d52836, d62608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d52836, d62608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro5759 (p : Pattern) (ha : d54673 p = 1) (hb : d62614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52749 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5755 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3571 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3571, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3571, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52816 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d52837 q = 1) (hb : d62609 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d52837, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52837, d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5758 q ha hb
  have h8 (q : Pattern) (ha : d3575 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3575, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5756 q ha hb
    | true =>
      simp only [d3575, d52850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5757 q ha hb
  have h9 (q : Pattern) (ha : d52851 q = 1) (hb : d62610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52851, d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52851, d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d52852 q = 1) (hb : d62611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52852, d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d52853 q = 1) (hb : d62612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d62612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52853, d62612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54672 q = 1) (hb : d62613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54672, d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54672, d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d54673 q = 1) (hb : d62614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54673, d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54673, d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h13 p ha hb
theorem andIntro5760 (p : Pattern) (ha : d54679 p = 1) (hb : d62620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54674 q = 1) (hb : d62615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54674, d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54674, d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5759 q ha hb
  have h2 (q : Pattern) (ha : d54675 q = 1) (hb : d62616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54675, d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54675, d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54676 q = 1) (hb : d62617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54676, d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54676, d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54677 q = 1) (hb : d62618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54677, d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54677, d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54678 q = 1) (hb : d62619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54678, d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54678, d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54679 q = 1) (hb : d62620 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54679, d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54679, d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5761 (p : Pattern) (ha : d2594 p = 1) (hb : d53080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53079 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2594 q = 1) (hb : d53080 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, d53080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2594, d53080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5762 (p : Pattern) (ha : d2594 p = 1) (hb : d53158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d53066 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d53066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d53067 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d53067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d53068 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d53068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d53069 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d53069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2594 q = 1) (hb : d53158 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, d53158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2594, d53158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5763 (p : Pattern) (ha : d3593 p = 1) (hb : d53164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53163 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3593 q = 1) (hb : d53164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3593, d53164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3593, d53164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5764 (p : Pattern) (ha : d53151 p = 1) (hb : d62624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d53088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro242 q ha hb
    | true =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d53089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d53090 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro244 q ha hb
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4525 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1797 q = 1) (hb : d53126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1798 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4526 q = 1) (hb : d53128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d53128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4526, d53128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51764 q = 1) (hb : d53129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51764, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51765 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51765, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d53150 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53151 q = 1) (hb : d62624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53151, d62624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d53151, d62624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro5765 (p : Pattern) (ha : d54684 p = 1) (hb : d62630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53070 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5761 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3590 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3590, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3590, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53131 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53152 q = 1) (hb : d62625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53152, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53152, d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5764 q ha hb
  have h8 (q : Pattern) (ha : d3594 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3594, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5762 q ha hb
    | true =>
      simp only [d3594, d53165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5763 q ha hb
  have h9 (q : Pattern) (ha : d53166 q = 1) (hb : d62626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53166, d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53166, d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53167 q = 1) (hb : d62627 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53167, d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d53168 q = 1) (hb : d62628 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d62628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53168, d62628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54683 q = 1) (hb : d62629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54683, d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54683, d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d54684 q = 1) (hb : d62630 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54684, d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54684, d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h13 p ha hb
theorem andIntro5766 (p : Pattern) (ha : d54690 p = 1) (hb : d62636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54685 q = 1) (hb : d62631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54685, d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54685, d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5765 q ha hb
  have h2 (q : Pattern) (ha : d54686 q = 1) (hb : d62632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54686, d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54686, d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54687 q = 1) (hb : d62633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54687, d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54687, d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54688 q = 1) (hb : d62634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54688, d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54688, d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54689 q = 1) (hb : d62635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54689, d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54689, d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54690 q = 1) (hb : d62636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54690, d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54690, d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5767 (p : Pattern) (ha : d2611 p = 1) (hb : d53401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53400 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2611 q = 1) (hb : d53401 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, d53401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2611, d53401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5768 (p : Pattern) (ha : d2611 p = 1) (hb : d53475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d53387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d53387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d53388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d53388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d53389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d53389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d53390 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d53390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2611 q = 1) (hb : d53475 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, d53475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2611, d53475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5769 (p : Pattern) (ha : d3613 p = 1) (hb : d53481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53480 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3613 q = 1) (hb : d53481 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3613, d53481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3613, d53481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5770 (p : Pattern) (ha : d53468 p = 1) (hb : d62641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d53409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro301 q ha hb
    | true =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d53410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d53411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro303 q ha hb
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d4566 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2275 q = 1) (hb : d53443 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d2276 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4567 q = 1) (hb : d53445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4567, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51793 q = 1) (hb : d53446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51793, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51794 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51794, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d53467 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d53468 q = 1) (hb : d62641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53468, d62641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d53468, d62641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro5771 (p : Pattern) (ha : d54696 p = 1) (hb : d62647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53391 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5767 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3610 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3610, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53448 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53469 q = 1) (hb : d62642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53469, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53469, d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5770 q ha hb
  have h8 (q : Pattern) (ha : d3614 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3614, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5768 q ha hb
    | true =>
      simp only [d3614, d53482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5769 q ha hb
  have h9 (q : Pattern) (ha : d53483 q = 1) (hb : d62643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53483, d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53483, d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d53484 q = 1) (hb : d62644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53484, d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d53485 q = 1) (hb : d62645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53485, d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54695 q = 1) (hb : d62646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54695, d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d54695, d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h13 (q : Pattern) (ha : d54696 q = 1) (hb : d62647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54696, d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d54696, d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h13 p ha hb
theorem andIntro5772 (p : Pattern) (ha : d54702 p = 1) (hb : d62653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54697 q = 1) (hb : d62648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54697, d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54697, d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5771 q ha hb
  have h2 (q : Pattern) (ha : d54698 q = 1) (hb : d62649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54698, d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54698, d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54699 q = 1) (hb : d62650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54699, d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54699, d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54700 q = 1) (hb : d62651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54700, d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54700, d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54701 q = 1) (hb : d62652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54701, d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54701, d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54702 q = 1) (hb : d62653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54702, d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54702, d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5773 (p : Pattern) (ha : d54708 p = 1) (hb : d62659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54661 q = 1) (hb : d62592 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54661, d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5742 q ha hb
    | true =>
      simp only [d54661, d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5748 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54670 q = 1) (hb : d62606 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54670, d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54670, d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5754 q ha hb
  have h3 (q : Pattern) (ha : d54671 q = 1) (hb : d62607 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54671, d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54671, d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54680 q = 1) (hb : d62621 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54680, d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54680, d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5760 q ha hb
  have h5 (q : Pattern) (ha : d54681 q = 1) (hb : d62622 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54681, d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54681, d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54682 q = 1) (hb : d62623 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54682, d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54682, d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54691 q = 1) (hb : d62637 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54691, d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54691, d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5766 q ha hb
  have h8 (q : Pattern) (ha : d54692 q = 1) (hb : d62638 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54692, d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54692, d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54693 q = 1) (hb : d62639 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54693, d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54693, d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54694 q = 1) (hb : d62640 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54694, d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54694, d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54703 q = 1) (hb : d62654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54703, d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54703, d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5772 q ha hb
  have h12 (q : Pattern) (ha : d54704 q = 1) (hb : d62655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54704, d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54704, d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54705 q = 1) (hb : d62656 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54705, d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54705, d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54706 q = 1) (hb : d62657 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54706, d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54706, d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54707 q = 1) (hb : d62658 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54707, d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54707, d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54708 q = 1) (hb : d62659 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54708, d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54708, d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5774 (p : Pattern) (ha : d54714 p = 1) (hb : d62665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54709 q = 1) (hb : d62660 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54709, d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5773 q ha hb
    | true =>
      simp only [d54709, d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54710 q = 1) (hb : d62661 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54710, d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54710, d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54711 q = 1) (hb : d62662 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54711, d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54711, d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54712 q = 1) (hb : d62663 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54712, d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54712, d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54713 q = 1) (hb : d62664 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54713, d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54713, d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54714 q = 1) (hb : d62665 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54714, d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54714, d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5775 (p : Pattern) (ha : d54720 p = 1) (hb : d62671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54715 q = 1) (hb : d62666 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54715, d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5774 q ha hb
    | true =>
      simp only [d54715, d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54716 q = 1) (hb : d62667 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54716, d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54716, d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54717 q = 1) (hb : d62668 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54717, d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54717, d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54718 q = 1) (hb : d62669 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54718, d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54718, d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54719 q = 1) (hb : d62670 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54719, d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54719, d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54720 q = 1) (hb : d62671 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54720, d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54720, d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5776 (p : Pattern) (ha : d54726 p = 1) (hb : d62677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54721 q = 1) (hb : d62672 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54721, d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5775 q ha hb
    | true =>
      simp only [d54721, d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54722 q = 1) (hb : d62673 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54722, d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54722, d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54723 q = 1) (hb : d62674 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54723, d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54723, d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54724 q = 1) (hb : d62675 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54724, d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54724, d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54725 q = 1) (hb : d62676 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54725, d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54725, d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54726 q = 1) (hb : d62677 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54726, d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54726, d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5777 (p : Pattern) (ha : d54732 p = 1) (hb : d62683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54727 q = 1) (hb : d62678 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54727, d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5776 q ha hb
    | true =>
      simp only [d54727, d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54728 q = 1) (hb : d62679 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54728, d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54728, d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54729 q = 1) (hb : d62680 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54729, d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54729, d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54730 q = 1) (hb : d62681 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54730, d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54730, d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54731 q = 1) (hb : d62682 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54731, d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54731, d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54732 q = 1) (hb : d62683 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54732, d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54732, d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5778 (p : Pattern) (ha : d54738 p = 1) (hb : d62689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54733 q = 1) (hb : d62684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54733, d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5777 q ha hb
    | true =>
      simp only [d54733, d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54734 q = 1) (hb : d62685 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54734, d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54734, d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54735 q = 1) (hb : d62686 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54735, d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54735, d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54736 q = 1) (hb : d62687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54736, d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54736, d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54737 q = 1) (hb : d62688 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54737, d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54737, d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54738 q = 1) (hb : d62689 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54738, d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54738, d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5779 (p : Pattern) (ha : d54744 p = 1) (hb : d62695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54739 q = 1) (hb : d62690 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54739, d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5778 q ha hb
    | true =>
      simp only [d54739, d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54740 q = 1) (hb : d62691 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54740, d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54740, d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54741 q = 1) (hb : d62692 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54741, d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54741, d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54742 q = 1) (hb : d62693 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54742, d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54742, d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54743 q = 1) (hb : d62694 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54743, d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54743, d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54744 q = 1) (hb : d62695 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54744, d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54744, d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5780 (p : Pattern) (ha : d54750 p = 1) (hb : d62701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54745 q = 1) (hb : d62696 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54745, d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5779 q ha hb
    | true =>
      simp only [d54745, d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54746 q = 1) (hb : d62697 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54746, d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54746, d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54747 q = 1) (hb : d62698 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54747, d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54747, d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54748 q = 1) (hb : d62699 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54748, d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54748, d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54749 q = 1) (hb : d62700 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54749, d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54749, d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54750 q = 1) (hb : d62701 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54750, d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54750, d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5781 (p : Pattern) (ha : d62821 p = 1) (hb : d62934 p = 1) : d62821 p = 1 := by
  have h0 (q : Pattern) (ha : d62821 q = 1) (hb : d62934 q = 1) : d62821 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro5782 (p : Pattern) (ha : d213 p = 1) (hb : d52029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d52009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d52009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d52010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d52010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d52010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d52011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52028 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d213 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, d52029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d213, d52029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro5783 (p : Pattern) (ha : d54639 p = 1) (hb : d62704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52013 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5782 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2527 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2527, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52035 q = 1) (hb : d62702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52035, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54638 q = 1) (hb : d62703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54638, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54638, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54639 q = 1) (hb : d62704 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54639, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54639, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5784 (p : Pattern) (ha : d2536 p = 1) (hb : d52161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d280 q = 1) (hb : d52137 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d280, d52137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d52140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d52140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281, d52140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d52141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52160 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2536 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, d52161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2536, d52161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5785 (p : Pattern) (ha : d54646 p = 1) (hb : d62712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52143 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5784 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2539 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2539, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52167 q = 1) (hb : d62710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52167, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54645 q = 1) (hb : d62711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54645, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54645, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54646 q = 1) (hb : d62712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54646, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54646, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5786 (p : Pattern) (ha : d54652 p = 1) (hb : d62718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54637 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54640 q = 1) (hb : d62705 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54640, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54640, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5783 q ha hb
  have h3 (q : Pattern) (ha : d54641 q = 1) (hb : d62706 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54641, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54641, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54642 q = 1) (hb : d62707 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54642, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54642, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54643 q = 1) (hb : d62708 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54643, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54643, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54644 q = 1) (hb : d62709 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54644, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54644, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54647 q = 1) (hb : d62713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54647, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54647, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5785 q ha hb
  have h8 (q : Pattern) (ha : d54648 q = 1) (hb : d62714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54648, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54648, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54649 q = 1) (hb : d62715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54649, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54649, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54650 q = 1) (hb : d62716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54650, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54650, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54651 q = 1) (hb : d62717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54651, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54651, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54652 q = 1) (hb : d62718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54652, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54652, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5787 (p : Pattern) (ha : d2549 p = 1) (hb : d52335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d492 q = 1) (hb : d52239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
    | true =>
      simp only [d492, d52239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h4 (q : Pattern) (ha : d493 q = 1) (hb : d52309 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d493, d52309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d52312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d52312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d494, d52312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d52313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52334 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2549 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, d52335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2549, d52335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5788 (p : Pattern) (ha : d54654 p = 1) (hb : d62721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5787 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2552 q = 1) (hb : d52351 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2552, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52352 q = 1) (hb : d62719 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52352, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54653 q = 1) (hb : d62720 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54653, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54653, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54654 q = 1) (hb : d62721 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54654, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54654, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5789 (p : Pattern) (ha : d54660 p = 1) (hb : d62727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54655 q = 1) (hb : d62722 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54655, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54655, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5788 q ha hb
  have h2 (q : Pattern) (ha : d54656 q = 1) (hb : d62723 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54656, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54656, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54657 q = 1) (hb : d62724 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54657, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54657, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54658 q = 1) (hb : d62725 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54658, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54658, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54659 q = 1) (hb : d62726 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54659, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54659, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54660 q = 1) (hb : d62727 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54660, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54660, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5790 (p : Pattern) (ha : d2563 p = 1) (hb : d52556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d784 q = 1) (hb : d52461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
    | true =>
      simp only [d784, d52461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h4 (q : Pattern) (ha : d785 q = 1) (hb : d52530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d785, d52530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d52533 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d52533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d786, d52533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d52534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52555 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2563 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, d52556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2563, d52556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5791 (p : Pattern) (ha : d54663 p = 1) (hb : d62731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52536 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5790 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2566 q = 1) (hb : d52572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2566, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52573 q = 1) (hb : d62729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52573, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54662 q = 1) (hb : d62730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54662, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54662, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54663 q = 1) (hb : d62731 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54663, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54663, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5792 (p : Pattern) (ha : d54669 p = 1) (hb : d62737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54664 q = 1) (hb : d62732 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54664, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54664, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5791 q ha hb
  have h2 (q : Pattern) (ha : d54665 q = 1) (hb : d62733 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54665, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54665, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54666 q = 1) (hb : d62734 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54666, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54666, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54667 q = 1) (hb : d62735 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54667, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54667, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54668 q = 1) (hb : d62736 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54668, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54668, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54669 q = 1) (hb : d62737 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54669, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54669, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5793 (p : Pattern) (ha : d2578 p = 1) (hb : d52836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1163 q = 1) (hb : d52744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
    | true =>
      simp only [d1163, d52744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h4 (q : Pattern) (ha : d1164 q = 1) (hb : d52810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1164, d52810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d52813 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d52813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1165, d52813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d52814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52835 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2578 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, d52836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2578, d52836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5794 (p : Pattern) (ha : d54673 p = 1) (hb : d62742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52816 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5793 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2581 q = 1) (hb : d52852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2581, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52853 q = 1) (hb : d62740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52853, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54672 q = 1) (hb : d62741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54672, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54672, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54673 q = 1) (hb : d62742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54673, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54673, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5795 (p : Pattern) (ha : d54679 p = 1) (hb : d62748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54674 q = 1) (hb : d62743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54674, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54674, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5794 q ha hb
  have h2 (q : Pattern) (ha : d54675 q = 1) (hb : d62744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54675, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54675, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54676 q = 1) (hb : d62745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54676, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54676, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54677 q = 1) (hb : d62746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54677, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54677, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54678 q = 1) (hb : d62747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54678, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54678, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54679 q = 1) (hb : d62748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54679, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54679, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5796 (p : Pattern) (ha : d2594 p = 1) (hb : d53151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1624 q = 1) (hb : d53065 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
    | true =>
      simp only [d1624, d53065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d53125 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1625, d53125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d53128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d53128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d53128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d53129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53150 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2594 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, d53151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2594, d53151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5797 (p : Pattern) (ha : d54684 p = 1) (hb : d62754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5796 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2597 q = 1) (hb : d53167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2597, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53168 q = 1) (hb : d62752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53168, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54683 q = 1) (hb : d62753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54683, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54683, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54684 q = 1) (hb : d62754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54684, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54684, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5798 (p : Pattern) (ha : d54690 p = 1) (hb : d62760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54685 q = 1) (hb : d62755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54685, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54685, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5797 q ha hb
  have h2 (q : Pattern) (ha : d54686 q = 1) (hb : d62756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54686, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54686, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54687 q = 1) (hb : d62757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54687, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54687, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54688 q = 1) (hb : d62758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54688, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54688, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54689 q = 1) (hb : d62759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54689, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54689, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54690 q = 1) (hb : d62760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54690, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54690, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5799 (p : Pattern) (ha : d2611 p = 1) (hb : d53468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2107 q = 1) (hb : d53386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
    | true =>
      simp only [d2107, d53386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d53442 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2108, d53442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d53445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d53445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d53446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53467 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2611 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, d53468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2611, d53468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5800 (p : Pattern) (ha : d54696 p = 1) (hb : d62767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5799 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2614 q = 1) (hb : d53484 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2614, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53485 q = 1) (hb : d62765 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53485, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54695 q = 1) (hb : d62766 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54695, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54695, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h9 (q : Pattern) (ha : d54696 q = 1) (hb : d62767 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54696, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54696, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h9 p ha hb
theorem andIntro5801 (p : Pattern) (ha : d54702 p = 1) (hb : d62773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54697 q = 1) (hb : d62768 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54697, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54697, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5800 q ha hb
  have h2 (q : Pattern) (ha : d54698 q = 1) (hb : d62769 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54698, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54698, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54699 q = 1) (hb : d62770 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54699, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54699, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54700 q = 1) (hb : d62771 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54700, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54700, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54701 q = 1) (hb : d62772 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54701, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54701, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54702 q = 1) (hb : d62773 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54702, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54702, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5802 (p : Pattern) (ha : d54708 p = 1) (hb : d62779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54661 q = 1) (hb : d62728 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54661, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5786 q ha hb
    | true =>
      simp only [d54661, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5789 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54670 q = 1) (hb : d62738 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54670, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54670, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5792 q ha hb
  have h3 (q : Pattern) (ha : d54671 q = 1) (hb : d62739 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54671, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54671, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54680 q = 1) (hb : d62749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54680, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54680, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5795 q ha hb
  have h5 (q : Pattern) (ha : d54681 q = 1) (hb : d62750 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54681, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54681, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54682 q = 1) (hb : d62751 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54682, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54682, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54691 q = 1) (hb : d62761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54691, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54691, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5798 q ha hb
  have h8 (q : Pattern) (ha : d54692 q = 1) (hb : d62762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54692, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54692, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54693 q = 1) (hb : d62763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54693, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54693, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54694 q = 1) (hb : d62764 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54694, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54694, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54703 q = 1) (hb : d62774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54703, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54703, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5801 q ha hb
  have h12 (q : Pattern) (ha : d54704 q = 1) (hb : d62775 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54704, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54704, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54705 q = 1) (hb : d62776 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54705, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54705, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54706 q = 1) (hb : d62777 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54706, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d54706, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54707 q = 1) (hb : d62778 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54707, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54707, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54708 q = 1) (hb : d62779 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54708, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54708, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5803 (p : Pattern) (ha : d54714 p = 1) (hb : d62785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54709 q = 1) (hb : d62780 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54709, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5802 q ha hb
    | true =>
      simp only [d54709, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54710 q = 1) (hb : d62781 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54710, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54710, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54711 q = 1) (hb : d62782 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54711, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54711, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54712 q = 1) (hb : d62783 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54712, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54712, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54713 q = 1) (hb : d62784 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54713, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54713, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54714 q = 1) (hb : d62785 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54714, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54714, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5804 (p : Pattern) (ha : d54720 p = 1) (hb : d62791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54715 q = 1) (hb : d62786 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54715, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5803 q ha hb
    | true =>
      simp only [d54715, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54716 q = 1) (hb : d62787 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54716, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54716, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54717 q = 1) (hb : d62788 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54717, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54717, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54718 q = 1) (hb : d62789 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54718, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54718, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54719 q = 1) (hb : d62790 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54719, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54719, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54720 q = 1) (hb : d62791 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54720, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54720, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5805 (p : Pattern) (ha : d54726 p = 1) (hb : d62797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54721 q = 1) (hb : d62792 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54721, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5804 q ha hb
    | true =>
      simp only [d54721, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54722 q = 1) (hb : d62793 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54722, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54722, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54723 q = 1) (hb : d62794 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54723, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54723, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54724 q = 1) (hb : d62795 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54724, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54724, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54725 q = 1) (hb : d62796 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54725, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54725, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54726 q = 1) (hb : d62797 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54726, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54726, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5806 (p : Pattern) (ha : d54732 p = 1) (hb : d62803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54727 q = 1) (hb : d62798 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54727, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5805 q ha hb
    | true =>
      simp only [d54727, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54728 q = 1) (hb : d62799 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54728, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54728, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54729 q = 1) (hb : d62800 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54729, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54729, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54730 q = 1) (hb : d62801 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54730, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54730, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54731 q = 1) (hb : d62802 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54731, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54731, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54732 q = 1) (hb : d62803 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54732, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54732, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5807 (p : Pattern) (ha : d54738 p = 1) (hb : d62809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54733 q = 1) (hb : d62804 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54733, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5806 q ha hb
    | true =>
      simp only [d54733, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54734 q = 1) (hb : d62805 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54734, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54734, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54735 q = 1) (hb : d62806 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54735, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54735, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54736 q = 1) (hb : d62807 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54736, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54736, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54737 q = 1) (hb : d62808 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54737, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54737, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54738 q = 1) (hb : d62809 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54738, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54738, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5808 (p : Pattern) (ha : d54744 p = 1) (hb : d62815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54739 q = 1) (hb : d62810 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54739, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5807 q ha hb
    | true =>
      simp only [d54739, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54740 q = 1) (hb : d62811 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54740, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54740, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54741 q = 1) (hb : d62812 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54741, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54741, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54742 q = 1) (hb : d62813 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54742, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54742, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54743 q = 1) (hb : d62814 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54743, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54743, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54744 q = 1) (hb : d62815 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54744, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54744, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5809 (p : Pattern) (ha : d54750 p = 1) (hb : d62821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54745 q = 1) (hb : d62816 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54745, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5808 q ha hb
    | true =>
      simp only [d54745, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54746 q = 1) (hb : d62817 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54746, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54746, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54747 q = 1) (hb : d62818 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54747, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54747, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54748 q = 1) (hb : d62819 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54748, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54748, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54749 q = 1) (hb : d62820 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54749, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54749, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54750 q = 1) (hb : d62821 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54750, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54750, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5810 (p : Pattern) (ha : d213 p = 1) (hb : d51646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d4335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d4336 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d51641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d51642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51645 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d213 q = 1) (hb : d51646 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, d51646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d213, d51646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5811 (p : Pattern) (ha : d54752 p = 1) (hb : d62704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51643 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2525 q = 1) (hb : d51647 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2525, d51647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5810 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2526 q = 1) (hb : d51648 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2526, d51648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2527 q = 1) (hb : d51649 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, d51649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2527, d51649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51650 q = 1) (hb : d62702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51650, d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54751 q = 1) (hb : d62703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54751, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54751, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54752 q = 1) (hb : d62704 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54752, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54752, d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5812 (p : Pattern) (ha : d2536 p = 1) (hb : d51663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d337 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d280 q = 1) (hb : d4371 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d280, d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d371 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d281 q = 1) (hb : d4372 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281, d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d282 q = 1) (hb : d51658 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d282, d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d283 q = 1) (hb : d51659 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51662 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2536 q = 1) (hb : d51663 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, d51663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2536, d51663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5813 (p : Pattern) (ha : d54759 p = 1) (hb : d62712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51660 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2537 q = 1) (hb : d51664 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2537, d51664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5812 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2538 q = 1) (hb : d51665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2538, d51665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2539 q = 1) (hb : d51666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, d51666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2539, d51666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51667 q = 1) (hb : d62710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51667, d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54758 q = 1) (hb : d62711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54758, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54758, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54759 q = 1) (hb : d62712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54759, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54759, d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5814 (p : Pattern) (ha : d54765 p = 1) (hb : d62718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2524 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54753 q = 1) (hb : d62705 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54753, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54753, d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5811 q ha hb
  have h3 (q : Pattern) (ha : d54754 q = 1) (hb : d62706 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54754, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54754, d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54755 q = 1) (hb : d62707 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54755, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54755, d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54756 q = 1) (hb : d62708 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54756, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54756, d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54757 q = 1) (hb : d62709 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54757, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d54757, d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54760 q = 1) (hb : d62713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54760, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54760, d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5813 q ha hb
  have h8 (q : Pattern) (ha : d54761 q = 1) (hb : d62714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54761, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54761, d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54762 q = 1) (hb : d62715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54762, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54762, d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54763 q = 1) (hb : d62716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54763, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54763, d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54764 q = 1) (hb : d62717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54764, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54764, d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54765 q = 1) (hb : d62718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54765, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54765, d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro5815 (p : Pattern) (ha : d2549 p = 1) (hb : d51688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d518 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d527 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d492 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d493 q = 1) (hb : d4408 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d493, d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d604 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d494 q = 1) (hb : d4409 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d494, d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d495 q = 1) (hb : d51683 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d495, d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d496 q = 1) (hb : d51684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51687 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2549 q = 1) (hb : d51688 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, d51688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2549, d51688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5816 (p : Pattern) (ha : d54767 p = 1) (hb : d62721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d510 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51685 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2550 q = 1) (hb : d51689 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2550, d51689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5815 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d645 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2551 q = 1) (hb : d51690 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2551, d51690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2552 q = 1) (hb : d51691 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, d51691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2552, d51691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51692 q = 1) (hb : d62719 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51692, d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54766 q = 1) (hb : d62720 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54766, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54766, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54767 q = 1) (hb : d62721 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54767, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54767, d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5817 (p : Pattern) (ha : d54773 p = 1) (hb : d62727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54768 q = 1) (hb : d62722 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54768, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54768, d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5816 q ha hb
  have h2 (q : Pattern) (ha : d54769 q = 1) (hb : d62723 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54769, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54769, d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54770 q = 1) (hb : d62724 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54770, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54770, d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54771 q = 1) (hb : d62725 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54771, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54771, d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54772 q = 1) (hb : d62726 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54772, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54772, d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54773 q = 1) (hb : d62727 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54773, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54773, d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5818 (p : Pattern) (ha : d2563 p = 1) (hb : d51714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d810 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d819 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d852 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d784 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d785 q = 1) (hb : d4446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d785, d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d910 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d786 q = 1) (hb : d4447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d786, d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d787 q = 1) (hb : d51709 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d787, d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d788 q = 1) (hb : d51710 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51713 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2563 q = 1) (hb : d51714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, d51714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2563, d51714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5819 (p : Pattern) (ha : d54776 p = 1) (hb : d62731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d802 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51711 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2564 q = 1) (hb : d51715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2564, d51715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5818 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d951 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2565 q = 1) (hb : d51716 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2565, d51716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2566 q = 1) (hb : d51717 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, d51717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2566, d51717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51718 q = 1) (hb : d62729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51718, d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54775 q = 1) (hb : d62730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54775, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54775, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54776 q = 1) (hb : d62731 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54776, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54776, d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5820 (p : Pattern) (ha : d54782 p = 1) (hb : d62737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54777 q = 1) (hb : d62732 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54777, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54777, d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5819 q ha hb
  have h2 (q : Pattern) (ha : d54778 q = 1) (hb : d62733 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54778, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54778, d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54779 q = 1) (hb : d62734 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54779, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54779, d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54780 q = 1) (hb : d62735 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54780, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54780, d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54781 q = 1) (hb : d62736 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54781, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54781, d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54782 q = 1) (hb : d62737 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54782, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54782, d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5821 (p : Pattern) (ha : d2578 p = 1) (hb : d51741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1189 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1228 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1163 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1164 q = 1) (hb : d4485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1164, d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1321 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1165 q = 1) (hb : d4486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1165, d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1166 q = 1) (hb : d51736 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1166, d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1167 q = 1) (hb : d51737 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51740 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2578 q = 1) (hb : d51741 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, d51741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2578, d51741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5822 (p : Pattern) (ha : d54786 p = 1) (hb : d62742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1181 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51738 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2579 q = 1) (hb : d51742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2579, d51742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5821 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1362 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2580 q = 1) (hb : d51743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2580, d51743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2581 q = 1) (hb : d51744 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, d51744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2581, d51744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51745 q = 1) (hb : d62740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51745, d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54785 q = 1) (hb : d62741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54785, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54785, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54786 q = 1) (hb : d62742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54786, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54786, d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5823 (p : Pattern) (ha : d54792 p = 1) (hb : d62748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54787 q = 1) (hb : d62743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54787, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54787, d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5822 q ha hb
  have h2 (q : Pattern) (ha : d54788 q = 1) (hb : d62744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54788, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54788, d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54789 q = 1) (hb : d62745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54789, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54789, d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54790 q = 1) (hb : d62746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54790, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54790, d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54791 q = 1) (hb : d62747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54791, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54791, d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54792 q = 1) (hb : d62748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54792, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54792, d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5824 (p : Pattern) (ha : d2594 p = 1) (hb : d51769 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1650 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1659 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1683 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1624 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d4525 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1625, d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1798 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1626 q = 1) (hb : d4526 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1627 q = 1) (hb : d51764 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1627, d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1628 q = 1) (hb : d51765 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51768 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2594 q = 1) (hb : d51769 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, d51769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2594, d51769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5825 (p : Pattern) (ha : d54797 p = 1) (hb : d62754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1642 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2595 q = 1) (hb : d51770 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2595, d51770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5824 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1839 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2596 q = 1) (hb : d51771 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2596, d51771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2597 q = 1) (hb : d51772 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, d51772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2597, d51772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51773 q = 1) (hb : d62752 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51773, d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54796 q = 1) (hb : d62753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54796, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54796, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54797 q = 1) (hb : d62754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54797, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54797, d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5826 (p : Pattern) (ha : d54803 p = 1) (hb : d62760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54798 q = 1) (hb : d62755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54798, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54798, d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5825 q ha hb
  have h2 (q : Pattern) (ha : d54799 q = 1) (hb : d62756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54799, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54799, d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54800 q = 1) (hb : d62757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54800, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54800, d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54801 q = 1) (hb : d62758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54801, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54801, d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54802 q = 1) (hb : d62759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54802, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54802, d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54803 q = 1) (hb : d62760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54803, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54803, d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5827 (p : Pattern) (ha : d2611 p = 1) (hb : d51798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2133 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2107 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d4566 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2108, d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d2276 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2109 q = 1) (hb : d4567 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2110 q = 1) (hb : d51793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2110, d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2111 q = 1) (hb : d51794 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51797 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2611 q = 1) (hb : d51798 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, d51798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2611, d51798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5828 (p : Pattern) (ha : d54809 p = 1) (hb : d62767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2125 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2612 q = 1) (hb : d51799 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2612, d51799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5827 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d2317 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2613 q = 1) (hb : d51800 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2613, d51800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2614 q = 1) (hb : d51801 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, d51801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2614, d51801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51802 q = 1) (hb : d62765 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51802, d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d54808 q = 1) (hb : d62766 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54808, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d54808, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d54809 q = 1) (hb : d62767 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d54809, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d54809, d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h9 p ha hb
theorem andIntro5829 (p : Pattern) (ha : d54815 p = 1) (hb : d62773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54810 q = 1) (hb : d62768 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d54810, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54810, d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5828 q ha hb
  have h2 (q : Pattern) (ha : d54811 q = 1) (hb : d62769 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d54811, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54811, d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54812 q = 1) (hb : d62770 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d54812, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54812, d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54813 q = 1) (hb : d62771 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d54813, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54813, d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54814 q = 1) (hb : d62772 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d54814, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54814, d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54815 q = 1) (hb : d62773 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d54815, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54815, d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5830 (p : Pattern) (ha : d54821 p = 1) (hb : d62779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54774 q = 1) (hb : d62728 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54774, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5814 q ha hb
    | true =>
      simp only [d54774, d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5817 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54783 q = 1) (hb : d62738 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54783, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54783, d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5820 q ha hb
  have h3 (q : Pattern) (ha : d54784 q = 1) (hb : d62739 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54784, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54784, d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54793 q = 1) (hb : d62749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54793, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54793, d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5823 q ha hb
  have h5 (q : Pattern) (ha : d54794 q = 1) (hb : d62750 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54794, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54794, d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54795 q = 1) (hb : d62751 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54795, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54795, d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54804 q = 1) (hb : d62761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54804, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54804, d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5826 q ha hb
  have h8 (q : Pattern) (ha : d54805 q = 1) (hb : d62762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54805, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54805, d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54806 q = 1) (hb : d62763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54806, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54806, d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54807 q = 1) (hb : d62764 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54807, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d54807, d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54816 q = 1) (hb : d62774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d54816, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54816, d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5829 q ha hb
  have h12 (q : Pattern) (ha : d54817 q = 1) (hb : d62775 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d54817, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54817, d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54818 q = 1) (hb : d62776 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d54818, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54818, d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54819 q = 1) (hb : d62777 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d54819, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54819, d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54820 q = 1) (hb : d62778 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d54820, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d54820, d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54821 q = 1) (hb : d62779 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d54821, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d54821, d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5831 (p : Pattern) (ha : d54827 p = 1) (hb : d62785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54822 q = 1) (hb : d62780 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d54822, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5830 q ha hb
    | true =>
      simp only [d54822, d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54823 q = 1) (hb : d62781 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d54823, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54823, d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54824 q = 1) (hb : d62782 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d54824, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54824, d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54825 q = 1) (hb : d62783 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d54825, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54825, d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54826 q = 1) (hb : d62784 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d54826, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54826, d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54827 q = 1) (hb : d62785 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d54827, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54827, d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5832 (p : Pattern) (ha : d54833 p = 1) (hb : d62791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54828 q = 1) (hb : d62786 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d54828, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5831 q ha hb
    | true =>
      simp only [d54828, d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54829 q = 1) (hb : d62787 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d54829, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54829, d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54830 q = 1) (hb : d62788 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d54830, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54830, d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54831 q = 1) (hb : d62789 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d54831, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54831, d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54832 q = 1) (hb : d62790 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d54832, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54832, d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54833 q = 1) (hb : d62791 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d54833, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54833, d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5833 (p : Pattern) (ha : d54839 p = 1) (hb : d62797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54834 q = 1) (hb : d62792 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d54834, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5832 q ha hb
    | true =>
      simp only [d54834, d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54835 q = 1) (hb : d62793 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d54835, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54835, d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54836 q = 1) (hb : d62794 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d54836, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54836, d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54837 q = 1) (hb : d62795 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d54837, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54837, d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54838 q = 1) (hb : d62796 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d54838, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54838, d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54839 q = 1) (hb : d62797 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d54839, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54839, d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5834 (p : Pattern) (ha : d54845 p = 1) (hb : d62803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54840 q = 1) (hb : d62798 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d54840, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5833 q ha hb
    | true =>
      simp only [d54840, d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54841 q = 1) (hb : d62799 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d54841, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54841, d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54842 q = 1) (hb : d62800 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d54842, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54842, d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54843 q = 1) (hb : d62801 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d54843, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54843, d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54844 q = 1) (hb : d62802 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d54844, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54844, d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54845 q = 1) (hb : d62803 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d54845, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54845, d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5835 (p : Pattern) (ha : d54851 p = 1) (hb : d62809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54846 q = 1) (hb : d62804 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d54846, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5834 q ha hb
    | true =>
      simp only [d54846, d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54847 q = 1) (hb : d62805 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d54847, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54847, d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54848 q = 1) (hb : d62806 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d54848, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54848, d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54849 q = 1) (hb : d62807 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d54849, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54849, d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54850 q = 1) (hb : d62808 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d54850, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54850, d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54851 q = 1) (hb : d62809 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d54851, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54851, d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5836 (p : Pattern) (ha : d54857 p = 1) (hb : d62815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54852 q = 1) (hb : d62810 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d54852, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5835 q ha hb
    | true =>
      simp only [d54852, d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54853 q = 1) (hb : d62811 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d54853, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54853, d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54854 q = 1) (hb : d62812 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d54854, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54854, d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54855 q = 1) (hb : d62813 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d54855, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54855, d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54856 q = 1) (hb : d62814 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d54856, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54856, d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54857 q = 1) (hb : d62815 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d54857, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54857, d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5837 (p : Pattern) (ha : d54863 p = 1) (hb : d62821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54858 q = 1) (hb : d62816 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d54858, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5836 q ha hb
    | true =>
      simp only [d54858, d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d54859 q = 1) (hb : d62817 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d54859, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d54859, d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d54860 q = 1) (hb : d62818 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d54860, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d54860, d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d54861 q = 1) (hb : d62819 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d54861, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d54861, d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d54862 q = 1) (hb : d62820 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54862, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54862, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d54863 q = 1) (hb : d62821 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d54863, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d54863, d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5838 (p : Pattern) (ha : d3503 p = 1) (hb : d54980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d3501 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3502 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3502, d54980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d3502, d54980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3503 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro5839 (p : Pattern) (ha : d54980 p = 1) (hb : d62560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5840 (p : Pattern) (ha : d54980 p = 1) (hb : d62572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62570 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62571 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62572 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5841 (p : Pattern) (ha : d54980 p = 1) (hb : d62578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3504 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5838 q ha hb
  have h2 (q : Pattern) (ha : d3505 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3506 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3507 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5839 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54980 q = 1) (hb : d62563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54980 q = 1) (hb : d62564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54980 q = 1) (hb : d62565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54980 q = 1) (hb : d62573 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5840 q ha hb
  have h11 (q : Pattern) (ha : d54980 q = 1) (hb : d62574 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d54980 q = 1) (hb : d62575 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54980 q = 1) (hb : d62576 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54980 q = 1) (hb : d62577 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54980 q = 1) (hb : d62578 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5842 (p : Pattern) (ha : d54980 p = 1) (hb : d62585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62583 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62584 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62585 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5843 (p : Pattern) (ha : d54980 p = 1) (hb : d62591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62586 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5842 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62587 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62588 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62589 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62590 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62591 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5844 (p : Pattern) (ha : d54980 p = 1) (hb : d62599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62597 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62598 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62599 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5845 (p : Pattern) (ha : d54980 p = 1) (hb : d62605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62600 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5844 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62601 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62602 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62603 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62604 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62605 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5846 (p : Pattern) (ha : d54980 p = 1) (hb : d62614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62612 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5847 (p : Pattern) (ha : d54980 p = 1) (hb : d62620 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5846 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62620 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5848 (p : Pattern) (ha : d54980 p = 1) (hb : d62630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62628 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62629 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62630 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5849 (p : Pattern) (ha : d54980 p = 1) (hb : d62636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62631 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5848 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62632 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62633 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62634 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62635 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62636 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5850 (p : Pattern) (ha : d54980 p = 1) (hb : d62647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62645 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5851 (p : Pattern) (ha : d54980 p = 1) (hb : d62653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5850 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5852 (p : Pattern) (ha : d54980 p = 1) (hb : d62659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54980 q = 1) (hb : d62592 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5841 q ha hb
    | true =>
      simp only [d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5843 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62606 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5845 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62607 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62621 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5847 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62622 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62623 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54980 q = 1) (hb : d62637 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5849 q ha hb
  have h8 (q : Pattern) (ha : d54980 q = 1) (hb : d62638 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54980 q = 1) (hb : d62639 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54980 q = 1) (hb : d62640 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54980 q = 1) (hb : d62654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5851 q ha hb
  have h12 (q : Pattern) (ha : d54980 q = 1) (hb : d62655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54980 q = 1) (hb : d62656 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54980 q = 1) (hb : d62657 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54980 q = 1) (hb : d62658 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54980 q = 1) (hb : d62659 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5853 (p : Pattern) (ha : d54980 p = 1) (hb : d62665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62660 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5852 q ha hb
    | true =>
      simp only [d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62661 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62662 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62663 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62664 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62665 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5854 (p : Pattern) (ha : d54980 p = 1) (hb : d62671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62666 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5853 q ha hb
    | true =>
      simp only [d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62667 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62668 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62669 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62670 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62671 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5855 (p : Pattern) (ha : d54980 p = 1) (hb : d62677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62672 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5854 q ha hb
    | true =>
      simp only [d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62673 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62674 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62675 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62676 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62677 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5856 (p : Pattern) (ha : d54980 p = 1) (hb : d62683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62678 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5855 q ha hb
    | true =>
      simp only [d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62679 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62680 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62681 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62682 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62683 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5857 (p : Pattern) (ha : d54980 p = 1) (hb : d62689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5856 q ha hb
    | true =>
      simp only [d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62685 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62686 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62688 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62689 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5858 (p : Pattern) (ha : d54980 p = 1) (hb : d62695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62690 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5857 q ha hb
    | true =>
      simp only [d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62691 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62692 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62693 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62694 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62695 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5859 (p : Pattern) (ha : d54981 p = 1) (hb : d62701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62696 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5858 q ha hb
    | true =>
      simp only [d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62697 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62698 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62699 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54981 q = 1) (hb : d62700 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54981, d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54981, d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d54981 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54981 q = 1) (hb : d62701 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro5860 (p : Pattern) (ha : d54980 p = 1) (hb : d62704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62702 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62704 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5861 (p : Pattern) (ha : d54980 p = 1) (hb : d62712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62710 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5862 (p : Pattern) (ha : d54980 p = 1) (hb : d62718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62705 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5860 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62706 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62707 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62708 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62709 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5861 q ha hb
  have h7 (q : Pattern) (ha : d54980 q = 1) (hb : d62714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d54980 q = 1) (hb : d62715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54980 q = 1) (hb : d62716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54980 q = 1) (hb : d62717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54980 q = 1) (hb : d62718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro5863 (p : Pattern) (ha : d54980 p = 1) (hb : d62721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62719 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62720 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62721 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5864 (p : Pattern) (ha : d54980 p = 1) (hb : d62727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62722 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5863 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62723 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62724 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62725 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62726 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62727 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5865 (p : Pattern) (ha : d54980 p = 1) (hb : d62731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62729 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62731 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5866 (p : Pattern) (ha : d54980 p = 1) (hb : d62737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62732 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5865 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62733 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62734 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62735 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62736 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62737 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5867 (p : Pattern) (ha : d54980 p = 1) (hb : d62742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62741 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62742 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5868 (p : Pattern) (ha : d54980 p = 1) (hb : d62748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62743 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5867 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62744 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62745 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62746 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62747 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62748 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5869 (p : Pattern) (ha : d54980 p = 1) (hb : d62754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62753 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62754 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5870 (p : Pattern) (ha : d54980 p = 1) (hb : d62760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5869 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62756 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62757 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62758 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62759 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62760 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5871 (p : Pattern) (ha : d54980 p = 1) (hb : d62767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62765 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62766 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d54980, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d54980, d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62767 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro5872 (p : Pattern) (ha : d54980 p = 1) (hb : d62773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62768 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5871 q ha hb
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62769 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62770 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62771 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62772 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62773 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5873 (p : Pattern) (ha : d54980 p = 1) (hb : d62779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d54980 q = 1) (hb : d62728 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5862 q ha hb
    | true =>
      simp only [d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5864 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62738 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5866 q ha hb
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62739 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62749 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5868 q ha hb
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62750 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62751 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d54980 q = 1) (hb : d62761 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5870 q ha hb
  have h8 (q : Pattern) (ha : d54980 q = 1) (hb : d62762 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d54980 q = 1) (hb : d62763 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d54980 q = 1) (hb : d62764 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d54980 q = 1) (hb : d62774 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5872 q ha hb
  have h12 (q : Pattern) (ha : d54980 q = 1) (hb : d62775 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d54980 q = 1) (hb : d62776 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d54980 q = 1) (hb : d62777 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d54980 q = 1) (hb : d62778 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d54980 q = 1) (hb : d62779 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro5874 (p : Pattern) (ha : d54980 p = 1) (hb : d62785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62780 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5873 q ha hb
    | true =>
      simp only [d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62781 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62782 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62783 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62784 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62785 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5875 (p : Pattern) (ha : d54980 p = 1) (hb : d62791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62786 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5874 q ha hb
    | true =>
      simp only [d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62787 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62788 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62789 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62790 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62791 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5876 (p : Pattern) (ha : d54980 p = 1) (hb : d62797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62792 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5875 q ha hb
    | true =>
      simp only [d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62793 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62794 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62795 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62796 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62797 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5877 (p : Pattern) (ha : d54980 p = 1) (hb : d62803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62798 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5876 q ha hb
    | true =>
      simp only [d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62799 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62800 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62801 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62802 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62803 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5878 (p : Pattern) (ha : d54980 p = 1) (hb : d62809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62804 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5877 q ha hb
    | true =>
      simp only [d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62805 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62806 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62807 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62808 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62809 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5879 (p : Pattern) (ha : d54980 p = 1) (hb : d62815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62810 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5878 q ha hb
    | true =>
      simp only [d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62811 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62812 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62813 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d54980 q = 1) (hb : d62814 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d54980 q = 1) (hb : d62815 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro5880 (p : Pattern) (ha : d54981 p = 1) (hb : d62821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d54980 q = 1) (hb : d62816 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5879 q ha hb
    | true =>
      simp only [d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d54980 q = 1) (hb : d62817 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d54980 q = 1) (hb : d62818 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d54980 q = 1) (hb : d62819 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d54981 q = 1) (hb : d62820 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d54981, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d54981, d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d54981 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d54981 q = 1) (hb : d62821 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro5881 (p : Pattern) (ha : d3497 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3497 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3497, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3497, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5882 (p : Pattern) (ha : d3503 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3498 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5881 q ha hb
  have h2 (q : Pattern) (ha : d3499 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3500 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3501 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3502 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3503 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5883 (p : Pattern) (ha : d62554 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2226 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2227 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2228 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62554 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62554, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62554, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5884 (p : Pattern) (ha : d62560 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2525 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5566 q ha hb
  have h2 (q : Pattern) (ha : d2526 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3508 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62555 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5883 q ha hb
  have h5 (q : Pattern) (ha : d214 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5566 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62556 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62557 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62558 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62559 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62560 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5885 (p : Pattern) (ha : d2536 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2228 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2219 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2536 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2536, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5886 (p : Pattern) (ha : d62566 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2235 q ha hb
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2226 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2236 q ha hb
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2227 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d337 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2237 q ha hb
    | true =>
      simp only [d337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2228 q ha hb
  have h9 (q : Pattern) (ha : d4371 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d370 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2228 q ha hb
    | true =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d371 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4372 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51658 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51659 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62566 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62566, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62566, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5887 (p : Pattern) (ha : d62572 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2537 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5885 q ha hb
  have h2 (q : Pattern) (ha : d2538 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3521 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62567 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5886 q ha hb
  have h5 (q : Pattern) (ha : d3524 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5885 q ha hb
    | true =>
      simp only [d3524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5566 q ha hb
  have h6 (q : Pattern) (ha : d62568 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62569 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62570 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62571 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62572 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5888 (p : Pattern) (ha : d62578 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3504 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5882 q ha hb
  have h2 (q : Pattern) (ha : d3505 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3506 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3507 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62561 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5884 q ha hb
  have h6 (q : Pattern) (ha : d62562 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62563 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62564 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62565 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62573 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5887 q ha hb
  have h11 (q : Pattern) (ha : d62574 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62575 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62576 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62577 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62578 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5889 (p : Pattern) (ha : d2549 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2242 q ha hb
    | true =>
      simp only [d492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2243 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2549 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2549, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5890 (p : Pattern) (ha : d3539 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2243 q ha hb
    | true =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3539 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3539, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3539, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5891 (p : Pattern) (ha : d62579 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d515 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2248 q ha hb
    | true =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2249 q ha hb
  have h2 (q : Pattern) (ha : d516 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d525 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2250 q ha hb
    | true =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2251 q ha hb
  have h6 (q : Pattern) (ha : d526 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d527 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d561 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2252 q ha hb
    | true =>
      simp only [d561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2242 q ha hb
  have h9 (q : Pattern) (ha : d4408 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d603 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2242 q ha hb
    | true =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d604 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4409 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51683 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51684 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62579 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62579, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62579, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5892 (p : Pattern) (ha : d62585 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2550 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5889 q ha hb
  have h2 (q : Pattern) (ha : d2551 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3536 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62580 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5891 q ha hb
  have h5 (q : Pattern) (ha : d3540 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5889 q ha hb
    | true =>
      simp only [d3540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5890 q ha hb
  have h6 (q : Pattern) (ha : d62581 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62582 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62583 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62584 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62585 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5893 (p : Pattern) (ha : d62591 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62586 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5892 q ha hb
  have h2 (q : Pattern) (ha : d62587 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62588 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62589 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62590 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62591 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5894 (p : Pattern) (ha : d2563 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2257 q ha hb
    | true =>
      simp only [d784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2258 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2563 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2563, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5895 (p : Pattern) (ha : d3556 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2258 q ha hb
    | true =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3556 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3556, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3556, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5896 (p : Pattern) (ha : d62593 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2263 q ha hb
    | true =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2264 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2265 q ha hb
    | true =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2266 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d852 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2267 q ha hb
    | true =>
      simp only [d852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2257 q ha hb
  have h9 (q : Pattern) (ha : d4446 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d909 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2257 q ha hb
    | true =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d910 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4447 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51709 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51710 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62593 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62593, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62593, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5897 (p : Pattern) (ha : d62599 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2564 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5894 q ha hb
  have h2 (q : Pattern) (ha : d2565 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3553 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62594 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5896 q ha hb
  have h5 (q : Pattern) (ha : d3557 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5894 q ha hb
    | true =>
      simp only [d3557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5895 q ha hb
  have h6 (q : Pattern) (ha : d62595 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62596 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62597 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62598 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62599 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5898 (p : Pattern) (ha : d62605 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62600 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5897 q ha hb
  have h2 (q : Pattern) (ha : d62601 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62602 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62603 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62604 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62605 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5899 (p : Pattern) (ha : d2578 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2272 q ha hb
    | true =>
      simp only [d1163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2273 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2578 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2578, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5900 (p : Pattern) (ha : d3574 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2273 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3574 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3574, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3574, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5901 (p : Pattern) (ha : d62608 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2278 q ha hb
    | true =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2279 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2280 q ha hb
    | true =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2281 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2282 q ha hb
    | true =>
      simp only [d1228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2272 q ha hb
  have h9 (q : Pattern) (ha : d4485 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1320 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2272 q ha hb
    | true =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1321 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4486 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51736 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51737 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62608 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62608, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62608, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5902 (p : Pattern) (ha : d62614 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2579 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5899 q ha hb
  have h2 (q : Pattern) (ha : d2580 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3571 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62609 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5901 q ha hb
  have h5 (q : Pattern) (ha : d3575 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5899 q ha hb
    | true =>
      simp only [d3575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5900 q ha hb
  have h6 (q : Pattern) (ha : d62610 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62611 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62612 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62613 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62614 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5903 (p : Pattern) (ha : d62620 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62615 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5902 q ha hb
  have h2 (q : Pattern) (ha : d62616 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62617 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62618 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62619 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62620 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5904 (p : Pattern) (ha : d2594 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2287 q ha hb
    | true =>
      simp only [d1624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2288 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2594 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2594, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5905 (p : Pattern) (ha : d3593 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2288 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3593 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3593, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3593, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5906 (p : Pattern) (ha : d62624 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2293 q ha hb
    | true =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2294 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2295 q ha hb
    | true =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2296 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2297 q ha hb
    | true =>
      simp only [d1683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2287 q ha hb
  have h9 (q : Pattern) (ha : d4525 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1797 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2287 q ha hb
    | true =>
      simp only [d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1798 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4526 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51764 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51765 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62624 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62624, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62624, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5907 (p : Pattern) (ha : d62630 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2595 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5904 q ha hb
  have h2 (q : Pattern) (ha : d2596 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3590 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62625 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5906 q ha hb
  have h5 (q : Pattern) (ha : d3594 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5904 q ha hb
    | true =>
      simp only [d3594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5905 q ha hb
  have h6 (q : Pattern) (ha : d62626 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62627 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62628 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62629 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62630 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5908 (p : Pattern) (ha : d62636 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62631 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5907 q ha hb
  have h2 (q : Pattern) (ha : d62632 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62633 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62634 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62635 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62636 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5909 (p : Pattern) (ha : d2611 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2302 q ha hb
    | true =>
      simp only [d2107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2303 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2611 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2611, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2611, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5910 (p : Pattern) (ha : d3613 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2303 q ha hb
    | true =>
      simp only [d2305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3613 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3613, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3613, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5911 (p : Pattern) (ha : d62641 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2308 q ha hb
    | true =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2309 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2310 q ha hb
    | true =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2311 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2312 q ha hb
    | true =>
      simp only [d2162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2302 q ha hb
  have h9 (q : Pattern) (ha : d4566 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d2275 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2302 q ha hb
    | true =>
      simp only [d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2276 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4567 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51793 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51794 q = 1) (hb : d62936 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62641 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62641, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62641, d73492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5912 (p : Pattern) (ha : d62647 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2612 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5909 q ha hb
  have h2 (q : Pattern) (ha : d2613 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3610 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62642 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5911 q ha hb
  have h5 (q : Pattern) (ha : d3614 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5909 q ha hb
    | true =>
      simp only [d3614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5910 q ha hb
  have h6 (q : Pattern) (ha : d62643 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62644 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62645 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62646 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62647 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5913 (p : Pattern) (ha : d62653 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62648 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5912 q ha hb
  have h2 (q : Pattern) (ha : d62649 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62650 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62651 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62652 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62653 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5914 (p : Pattern) (ha : d62659 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62592 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5888 q ha hb
    | true =>
      simp only [d62592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5893 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62606 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5898 q ha hb
  have h3 (q : Pattern) (ha : d62607 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62621 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5903 q ha hb
  have h5 (q : Pattern) (ha : d62622 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62623 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62637 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5908 q ha hb
  have h8 (q : Pattern) (ha : d62638 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62639 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62640 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62654 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5913 q ha hb
  have h12 (q : Pattern) (ha : d62655 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62656 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62657 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62658 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62659 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5915 (p : Pattern) (ha : d62665 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62660 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5914 q ha hb
    | true =>
      simp only [d62660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62661 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62662 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62663 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62664 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62665 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5916 (p : Pattern) (ha : d62671 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62666 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5915 q ha hb
    | true =>
      simp only [d62666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62667 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62668 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62669 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62670 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62671 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5917 (p : Pattern) (ha : d62677 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62672 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5916 q ha hb
    | true =>
      simp only [d62672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62673 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62674 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62675 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62676 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62677 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5918 (p : Pattern) (ha : d62683 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62678 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5917 q ha hb
    | true =>
      simp only [d62678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62679 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62680 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62681 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62682 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62683 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5919 (p : Pattern) (ha : d62689 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62684 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5918 q ha hb
    | true =>
      simp only [d62684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62685 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62686 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62687 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62688 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62689 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5920 (p : Pattern) (ha : d62695 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62690 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5919 q ha hb
    | true =>
      simp only [d62690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62691 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62692 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62693 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62694 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62695 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5921 (p : Pattern) (ha : d62701 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62696 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5920 q ha hb
    | true =>
      simp only [d62696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62697 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62698 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62699 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62700 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62701 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5922 (p : Pattern) (ha : d62704 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2525 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5566 q ha hb
  have h2 (q : Pattern) (ha : d2526 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2527 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62702 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62703 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62704 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5923 (p : Pattern) (ha : d62712 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2537 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5885 q ha hb
  have h2 (q : Pattern) (ha : d2538 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2539 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62710 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62711 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62712 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5924 (p : Pattern) (ha : d62718 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62705 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5922 q ha hb
  have h2 (q : Pattern) (ha : d62706 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62707 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62708 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62709 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62713 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5923 q ha hb
  have h7 (q : Pattern) (ha : d62714 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62715 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62716 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62717 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62718 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro5925 (p : Pattern) (ha : d62721 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2550 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5889 q ha hb
  have h2 (q : Pattern) (ha : d2551 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2552 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62719 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62720 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62721 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5926 (p : Pattern) (ha : d62727 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62722 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5925 q ha hb
  have h2 (q : Pattern) (ha : d62723 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62724 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62725 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62726 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62727 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5927 (p : Pattern) (ha : d62731 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2564 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5894 q ha hb
  have h2 (q : Pattern) (ha : d2565 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2566 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62729 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62730 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62731 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5928 (p : Pattern) (ha : d62737 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62732 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5927 q ha hb
  have h2 (q : Pattern) (ha : d62733 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62734 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62735 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62736 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62737 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5929 (p : Pattern) (ha : d62742 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2579 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5899 q ha hb
  have h2 (q : Pattern) (ha : d2580 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2581 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62740 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62741 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62742 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5930 (p : Pattern) (ha : d62748 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62743 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5929 q ha hb
  have h2 (q : Pattern) (ha : d62744 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62745 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62746 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62747 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62748 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5931 (p : Pattern) (ha : d62754 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2595 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5904 q ha hb
  have h2 (q : Pattern) (ha : d2596 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2597 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62752 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62753 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62754 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5932 (p : Pattern) (ha : d62760 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62755 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5931 q ha hb
  have h2 (q : Pattern) (ha : d62756 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62757 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62758 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62759 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62760 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5933 (p : Pattern) (ha : d62767 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2612 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5909 q ha hb
  have h2 (q : Pattern) (ha : d2613 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2614 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62765 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62766 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62767 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5934 (p : Pattern) (ha : d62773 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62768 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5933 q ha hb
  have h2 (q : Pattern) (ha : d62769 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62770 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62771 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62772 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62773 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5935 (p : Pattern) (ha : d62779 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d62728 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5924 q ha hb
    | true =>
      simp only [d62728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5926 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d62738 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5928 q ha hb
  have h3 (q : Pattern) (ha : d62739 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62749 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5930 q ha hb
  have h5 (q : Pattern) (ha : d62750 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62751 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62761 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5932 q ha hb
  have h8 (q : Pattern) (ha : d62762 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62763 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62764 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d62774 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5934 q ha hb
  have h12 (q : Pattern) (ha : d62775 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62776 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62777 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62778 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d62778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d62779 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d62779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro5936 (p : Pattern) (ha : d62785 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62780 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5935 q ha hb
    | true =>
      simp only [d62780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62781 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62782 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62783 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62784 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62785 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5937 (p : Pattern) (ha : d62791 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62786 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5936 q ha hb
    | true =>
      simp only [d62786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62787 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62788 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62789 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62790 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62791 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5938 (p : Pattern) (ha : d62797 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62792 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5937 q ha hb
    | true =>
      simp only [d62792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62793 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62794 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62795 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62796 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62797 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5939 (p : Pattern) (ha : d62803 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62798 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5938 q ha hb
    | true =>
      simp only [d62798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62799 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62800 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62801 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62802 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62803 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5940 (p : Pattern) (ha : d62809 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62804 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5939 q ha hb
    | true =>
      simp only [d62804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62805 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62806 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62807 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62808 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62809 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5941 (p : Pattern) (ha : d62815 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62810 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5940 q ha hb
    | true =>
      simp only [d62810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62811 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62812 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62813 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62814 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62815 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5942 (p : Pattern) (ha : d62821 p = 1) (hb : d73492 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62816 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5941 q ha hb
    | true =>
      simp only [d62816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d62817 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d62817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d62818 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d62818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d62819 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d62820 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62821 q = 1) (hb : d73492 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d62821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5943 (p : Pattern) (ha : d42 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d37 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d39 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d40 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d41 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d41, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d42 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5944 (p : Pattern) (ha : d3497 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5943 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d45 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d45, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d46 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3497 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3497, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3497, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5945 (p : Pattern) (ha : d3503 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3498 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5944 q ha hb
  have h2 (q : Pattern) (ha : d3499 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3500 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3501 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3502 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3503 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro5946 (p : Pattern) (ha : d213 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5943 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d100 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d103 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d213 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d213, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5947 (p : Pattern) (ha : d116 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d37 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d39 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d40 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d40, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d115 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d116, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d116, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5948 (p : Pattern) (ha : d123 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d37 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d39 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d39, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d121 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d123 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5949 (p : Pattern) (ha : d156 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d152 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d37 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d38 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d153 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d154 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d156 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5950 (p : Pattern) (ha : d62554 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5947 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5948 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d157 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5949 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5943 q ha hb
  have h9 (q : Pattern) (ha : d4335 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5943 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62554 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62554, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62554, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5951 (p : Pattern) (ha : d62560 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2525 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5946 q ha hb
  have h2 (q : Pattern) (ha : d2526 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3508 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62555 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5950 q ha hb
  have h5 (q : Pattern) (ha : d214 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5946 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d62556 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62557 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62558 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62559 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62560 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5952 (p : Pattern) (ha : d2536 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5949 q ha hb
    | true =>
      simp only [d157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5943 q ha hb
  have h2 (q : Pattern) (ha : d280 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d281 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d282 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d283 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2536 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2536, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2536, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5953 (p : Pattern) (ha : d296 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d151 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d152, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d37 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d38 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d153 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d154 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d295 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d296 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5954 (p : Pattern) (ha : d303 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d151 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d152, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d37 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d38 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d38, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d153 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d301 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d302 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d303 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5955 (p : Pattern) (ha : d336 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d332 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d332, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d151 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d152 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d152, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d333 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d334 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d335 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d336 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d336, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d336, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5956 (p : Pattern) (ha : d62566 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d297 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5953 q ha hb
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5947 q ha hb
  have h2 (q : Pattern) (ha : d298 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d299 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d300 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d304 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5954 q ha hb
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5948 q ha hb
  have h6 (q : Pattern) (ha : d305 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d306 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d337 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5955 q ha hb
    | true =>
      simp only [d337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5949 q ha hb
  have h9 (q : Pattern) (ha : d4371 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d370 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5949 q ha hb
    | true =>
      simp only [d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d371 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4372 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51658 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51659 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62566 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62566, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62566, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5957 (p : Pattern) (ha : d62572 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2537 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5952 q ha hb
  have h2 (q : Pattern) (ha : d2538 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3521 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62567 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5956 q ha hb
  have h5 (q : Pattern) (ha : d3524 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5952 q ha hb
    | true =>
      simp only [d3524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5946 q ha hb
  have h6 (q : Pattern) (ha : d62568 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62569 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62570 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62571 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62572 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5958 (p : Pattern) (ha : d62578 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3504 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5945 q ha hb
  have h2 (q : Pattern) (ha : d3505 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3506 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3507 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62561 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5951 q ha hb
  have h6 (q : Pattern) (ha : d62562 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62563 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d62564 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62565 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d62573 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5957 q ha hb
  have h11 (q : Pattern) (ha : d62574 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d62575 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d62576 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d62577 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d62578 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro5959 (p : Pattern) (ha : d487 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d483 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d484 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d485 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d486 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d487 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d487, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d487, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5960 (p : Pattern) (ha : d491 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d488 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d489 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d490 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d491 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5961 (p : Pattern) (ha : d2549 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d492 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5959 q ha hb
    | true =>
      simp only [d492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5960 q ha hb
  have h2 (q : Pattern) (ha : d493 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d494 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d495 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d496 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2549 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2549, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2549, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5962 (p : Pattern) (ha : d3539 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5960 q ha hb
    | true =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3539 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3539, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3539, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5963 (p : Pattern) (ha : d512 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d478 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d479 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d479, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d483 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d484 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d485 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d511 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d512 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d512, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d512, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5964 (p : Pattern) (ha : d514 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d488 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d489 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d513 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d514 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5965 (p : Pattern) (ha : d521 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d478 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d479 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d479, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d483 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d484 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d519 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d520 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d521 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d521, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d521, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5966 (p : Pattern) (ha : d524 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d482 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d483, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d488 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d522 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d523 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d524 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5967 (p : Pattern) (ha : d560 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d556 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d556, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d478 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d479 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d557 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d558 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d559 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d560 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d560, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d560, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5968 (p : Pattern) (ha : d62579 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d515 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5963 q ha hb
    | true =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5964 q ha hb
  have h2 (q : Pattern) (ha : d516 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d517 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d518 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d525 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5965 q ha hb
    | true =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5966 q ha hb
  have h6 (q : Pattern) (ha : d526 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d527 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d561 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5967 q ha hb
    | true =>
      simp only [d561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5959 q ha hb
  have h9 (q : Pattern) (ha : d4408 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d603 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5959 q ha hb
    | true =>
      simp only [d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d604 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4409 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51683 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51684 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62579 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62579, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62579, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5969 (p : Pattern) (ha : d62585 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2550 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5961 q ha hb
  have h2 (q : Pattern) (ha : d2551 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3536 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62580 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5968 q ha hb
  have h5 (q : Pattern) (ha : d3540 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5961 q ha hb
    | true =>
      simp only [d3540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5962 q ha hb
  have h6 (q : Pattern) (ha : d62581 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62582 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62583 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62584 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62585 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5970 (p : Pattern) (ha : d62591 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62586 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5969 q ha hb
  have h2 (q : Pattern) (ha : d62587 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62588 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62589 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62590 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62591 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5971 (p : Pattern) (ha : d779 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d775 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d776 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d777 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d778 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d779 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d779, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d779, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5972 (p : Pattern) (ha : d783 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d780 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d781 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d782 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d783 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5973 (p : Pattern) (ha : d2563 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d784 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5971 q ha hb
    | true =>
      simp only [d784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5972 q ha hb
  have h2 (q : Pattern) (ha : d785 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d786 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d787 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d788 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2563 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2563, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2563, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5974 (p : Pattern) (ha : d3556 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5972 q ha hb
    | true =>
      simp only [d939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3556 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3556, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3556, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5975 (p : Pattern) (ha : d804 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d770 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d771 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d771, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d775 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d776 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d777 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d803 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d804 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d804, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d804, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5976 (p : Pattern) (ha : d806 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d780 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d781 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d805 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d806 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5977 (p : Pattern) (ha : d813 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d770 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d771 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d771, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d775 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d776 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d811 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d812 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d813 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d813, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d813, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5978 (p : Pattern) (ha : d816 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d774 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d775, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d780 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d814 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d815 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d816 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5979 (p : Pattern) (ha : d851 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d846 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d847 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d847, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d770 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d771 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d848 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d849 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d850 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d851 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d851, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d851, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5980 (p : Pattern) (ha : d62593 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5975 q ha hb
    | true =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5976 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5977 q ha hb
    | true =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5978 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d852 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5979 q ha hb
    | true =>
      simp only [d852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5971 q ha hb
  have h9 (q : Pattern) (ha : d4446 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d909 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5971 q ha hb
    | true =>
      simp only [d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d910 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4447 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51709 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51710 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62593 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62593, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62593, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5981 (p : Pattern) (ha : d62599 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2564 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5973 q ha hb
  have h2 (q : Pattern) (ha : d2565 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3553 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62594 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5980 q ha hb
  have h5 (q : Pattern) (ha : d3557 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5973 q ha hb
    | true =>
      simp only [d3557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5974 q ha hb
  have h6 (q : Pattern) (ha : d62595 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62596 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62597 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62598 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62599 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5982 (p : Pattern) (ha : d62605 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62600 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5981 q ha hb
  have h2 (q : Pattern) (ha : d62601 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62602 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62603 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62604 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62605 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5983 (p : Pattern) (ha : d1158 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1149 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1154 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1155 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1156 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1157 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d1158 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1158, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1158, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5984 (p : Pattern) (ha : d1162 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1159 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1160 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d1161 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d1162 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5985 (p : Pattern) (ha : d2578 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5983 q ha hb
    | true =>
      simp only [d1163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5984 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2578 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2578, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2578, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5986 (p : Pattern) (ha : d3574 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5984 q ha hb
    | true =>
      simp only [d1350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3574 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3574, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3574, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5987 (p : Pattern) (ha : d1183 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1149 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1150 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1150, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1154 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1155 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1156 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1182 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1183 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1183, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1183, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5988 (p : Pattern) (ha : d1185 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1159 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1160 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1184 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1185 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5989 (p : Pattern) (ha : d1192 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1149 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1150 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1150, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1154 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1155 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1190 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1191 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d1192 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1192, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1192, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5990 (p : Pattern) (ha : d1195 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1153 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1154, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1159 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d1193 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1194 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d1195 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5991 (p : Pattern) (ha : d1227 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1222 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1223 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1223, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1149 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1150 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1224 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1225 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1226 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d1227 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1227, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1227, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5992 (p : Pattern) (ha : d62608 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5987 q ha hb
    | true =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5988 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5989 q ha hb
    | true =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5990 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5991 q ha hb
    | true =>
      simp only [d1228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5983 q ha hb
  have h9 (q : Pattern) (ha : d4485 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d1320 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5983 q ha hb
    | true =>
      simp only [d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1321 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4486 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51736 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51737 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d62608 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d62608, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d62608, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro5993 (p : Pattern) (ha : d62614 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2579 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5985 q ha hb
  have h2 (q : Pattern) (ha : d2580 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3571 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62609 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5992 q ha hb
  have h5 (q : Pattern) (ha : d3575 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5985 q ha hb
    | true =>
      simp only [d3575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5986 q ha hb
  have h6 (q : Pattern) (ha : d62610 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d62610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d62611 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d62611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d62612 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d62612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d62613 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d62613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d62614 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d62614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro5994 (p : Pattern) (ha : d62620 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d62615 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5993 q ha hb
  have h2 (q : Pattern) (ha : d62616 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d62617 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d62618 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d62619 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d62620 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d62620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro5995 (p : Pattern) (ha : d1619 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1610 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1615 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d1616 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1617 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1618 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d1619 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1619, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1619, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro5996 (p : Pattern) (ha : d1623 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1620 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1621 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d1622 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d1623 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro5997 (p : Pattern) (ha : d2594 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5995 q ha hb
    | true =>
      simp only [d1624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5996 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2594 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2594, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2594, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5998 (p : Pattern) (ha : d3593 p = 1) (hb : d73777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5996 q ha hb
    | true =>
      simp only [d1827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3593 q = 1) (hb : d73777 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3593, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3593, d73777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro5999 (p : Pattern) (ha : d1644 p = 1) (hb : d73776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1610 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1611 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1611, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d1614 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1615 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1615, d73774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1616 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1617 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1643 q = 1) (hb : d73774 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1644 q = 1) (hb : d73776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1644, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1644, d73776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
end NetHack.Soko22Hazard87
